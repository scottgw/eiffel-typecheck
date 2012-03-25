{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Language.Eiffel.TypeCheck.Expr 
       (typeOfExpr, typeOfExprIs, clause, unlikeDecls, flatten) where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.Reader

import Debug.Trace

import Data.Maybe

import Language.Eiffel.Syntax
import Language.Eiffel.Position
import Language.Eiffel.Util

import qualified Language.Eiffel.TypeCheck.TypedExpr as T
import Language.Eiffel.TypeCheck.TypedExpr (TExpr)
import Language.Eiffel.TypeCheck.BasicTypes
import Language.Eiffel.TypeCheck.Context
import Language.Eiffel.TypeCheck.Generic

import Util.Monad

debug' str x = do
  typ <- current <$> ask
  case typ of
    ClassType cName _ ->
      if cName == str 
      then trace ("Tracing " ++ cName) x
      else x
    _ -> x

clause :: Clause Expr -> TypingBody body (Clause TExpr)
clause (Clause n e) =
  Clause n <$> typeOfExprIs boolType e

-- | Determine whether a given string (for a VarOrCall) is a call or
-- a local variable of some sort.
convertVarCall :: String -> TypingBody body (Maybe TExpr)
convertVarCall name = do
  curr <- current <$> ask
  flatCls <- flatten curr
  case findFeatureEx flatCls name of
    Nothing -> 
      do vTyp <- typeOfVar name
         maybeTag (T.Var name <$> vTyp)
    Just _ -> Just <$> expr (UnqualCall name []) -- compCall trg' name

maybeTag :: Maybe a -> TypingBody ctxBody (Maybe (Pos a))
maybeTag Nothing  = return Nothing
maybeTag (Just x) = Just <$> tagPos x

typeOfExpr :: Expr -> TypingBody body TExpr
typeOfExpr e = setPosition (position e) 
               (catchError (expr (contents e))
                           (\str -> throwError $ 
                                    str ++ " at " ++ show (position e)))

typeOfExprIs :: Typ -> Expr -> TypingBody body TExpr
typeOfExprIs typ expr = do
  e' <- typeOfExpr expr
  _  <- guardTypeIs typ e'
  return e'

expr :: forall body . UnPosExpr -> TypingBody body TExpr
expr (LitInt i)    = tagPos (T.LitInt i)
expr (LitDouble d) = tagPos (T.LitDouble d)
expr (LitBool b)   = tagPos (T.LitBool b)
expr LitVoid       = tagPos (T.LitVoid VoidType)
expr (LitString s) = tagPos (T.LitString s)
expr (LitChar c)   = tagPos (T.LitChar c)
expr CurrentVar    = currentM
expr ResultVar     = do
  res <- result <$> ask
  curr <- current <$> ask
  flatClas <- flatten curr
  unlikedRes <- unlikeType curr flatClas res
  tagPos (T.ResultVar unlikedRes)
expr (StaticCall typ name args) = do
  flatClas <- flatten typ
  case findFeatureEx flatClas name of
    Nothing -> 
      throwError (show typ ++ ": does not contain static call " ++ name)
    Just feat-> do 
      args' <- mapM typeOfExpr args
      let argTypes = map declType (featureArgs feat)
      argsConform args' argTypes
      tagPos (T.StaticCall typ name args' (featureResult feat))
                   
expr (VarOrCall s) = do
  exprMb <- convertVarCall s
  c <- currentM
  maybe (throwError ("TypeCheckc.Expr.expr: Can't resolve " ++ s ++ " from " ++ show c)) return exprMb

expr (Attached typeMb attch asMb) = do
  --TODO: Decide if we have to do any checking between typeMb and attch
  attch' <- typeOfExpr attch
  curr <- current <$> ask
  flatClas <- flatten curr
  typeMb' <- case typeMb of
      Nothing -> return Nothing 
      Just typ -> Just <$> unlikeType curr flatClas typ
  tagPos $ T.Attached typeMb' attch' asMb

expr (UnOpExpr op e)
  | op == Old = do
    e' <- typeOfExpr e
    tagPos (T.Old e')
  | otherwise = do
    e' <- typeOfExpr e
    cls <- lookupClass (T.texpr e')
    case findOperator cls (unOpAlias op) 0 of
      Nothing -> 
        throwError 
        ("No feature found associated with unary operator " ++ show op ++ " in " ++ show (T.texpr e'))
      Just f -> expr (QualCall e (featureName f) [])

expr (BinOpExpr op e1 e2) 
  | equalityOp op = do
    e1' <- typeOfExpr e1
    e2' <- typeOfExpr e2
    tagPos (T.EqExpr (T.eqOp op) e1' e2')
  | otherwise = do
    e1' <- debug' "ARRAY" $ typeOfExpr e1

    let
      attLocals :: Maybe Typ -> T.TExpr -> Maybe String ->
                   TypingBody body a -> TypingBody body a
      attLocals typeMb attch asMb m =
        let attTyp = fromMaybe (T.texpr attch) typeMb
        in case asMb of 
          Just as -> local (addDecls [Decl as attTyp]) m
          Nothing -> m

      extraLocals :: TypingBody body a -> TypingBody body a
      extraLocals =
          case contents e1' of
            T.Attached typeMb attch asMb -> attLocals typeMb attch asMb
            T.Call trg "negated" [] _ -> case contents trg of
              T.Attached typeMb attch asNameMb -> \ m ->
                do attTypeMb <- maybe (return Nothing) typeOfVar asNameMb
                   maybe (attLocals typeMb attch asNameMb m) (const m) attTypeMb
              _ -> id
            _ -> id
    flatCls <- flatten (T.texpr e1')
    case findOperator flatCls (opAlias op) 1 of
      Nothing -> throwError $ "Operator " ++ show op ++ " not found"
      Just feat -> extraLocals (expr $ QualCall e1 (featureName feat) [e2])

expr (UnqualCall fName args) = do
  qual <- QualCall <$> tagPos CurrentVar 
                   <*> pure fName 
                   <*> pure args
  expr qual
  
expr (QualCall trg name args) = do 
  -- typecheck and cast the target if from a generic class
  trg' <- typeOfExpr trg
  args' <- mapM typeOfExpr args

  let targetType = T.texpr trg'
  curr <- current <$> ask

  let inArray = case curr of
        ClassType "ARRAY" _ -> False -- True
        _ -> False
      dbg str x = if inArray then trace str x else x

  flatCls  <- if inArray 
              then currentPos >>= \p -> trace (show p ++ "," ++ name ++ ":" ++ show targetType) $ flatten targetType 
              else flatten targetType
  
  case dbg ("findFeatureEx: " ++ name) $ findFeatureEx flatCls name of
    Nothing -> throwError $ "expr.QualCall: " ++ show trg' ++ ": " ++ name ++ show args' ++ show (map featureName $ allRoutines flatCls)
    Just feat ->
      let formArgs = map declType (featureArgs feat)
          res = featureResult feat
      in catchError 
         (do argsConform args' formArgs
             tagPos (T.Call trg' name args' res)
         )
         (\e -> case args' of
             [arg] -> 
               if contents arg `numericCanBe` targetType
               then do -- check to see if the numeric types can 
                       -- be casted to one another
                 arg' <- dbg "first if" $ tagPos (T.Cast targetType arg)
                 tagPos (T.Call trg' name [arg'] res)
               else if contents trg' `numericCanBe` T.texpr arg 
                    then do 
                      trg'' <- dbg "second if" $ tagPos (T.Cast (T.texpr arg) trg')
                      tagPos (T.Call trg'' name [arg] res)
                    else throwError $ e ++ " AND! " ++ show (trg',name,args, targetType) -- throwError $ e ++ " AND! " ++ show (trg',name,args, targetType, formArgs, map (\f -> (featureName f, featureArgs f)) $ allRoutines flatCls)
                      -- catchError (
                      --   do castedTrg <- conformThrow trg' (T.texpr arg)
                      --      expr (QualCall (T.untypeExpr castedTrg) name args))
                      --   (\ _ -> throwError $ e ++ " AND! " ++ show (trg',name,args, targetType))
             _ -> throwError e
         )
expr (CreateExpr typ name args) = do
  -- this comes basically from the above 
  -- see if the call is valid wth the args proposed
  flatCls <- flatten typ
  
  case findFeatureEx flatCls name of
    Nothing -> throwError $ "expr:CreateExpr no procedure " ++ name
    Just feat -> do
      -- typecheck and cast the arguments if they come from a generic class
      args'   <- mapM typeOfExpr args
      argsConform args' (map declType (featureArgs feat))
      tagPos (T.CreateExpr typ name args')
expr (LitType t) = tagPos (T.LitType t)

expr (Agent e) = do
  (trg, name, args) <- case contents e of
    QualCall trg name args -> (, name, args) <$> typeOfExpr trg
    UnqualCall name args -> (, name, args) <$> expr CurrentVar
    VarOrCall name -> (, name, []) <$> expr CurrentVar
  
  let trgType = T.texpr trg
      filledArgs = filter ((/= (VarOrCall "?")) . contents) args
      
  args' <- mapM typeOfExpr filledArgs
  
  flatCls <- flatten trgType
  case findFeatureEx flatCls name of
    Nothing -> error $ "expr.Agent: " ++ show trgType
    Just feat ->
      let
        featArgs = featureArgs feat
        withMissingArgs = if length args == 0 && length featArgs /= 0
                          then replicate (length featArgs) (VarOrCall "?")
                          else map contents args
        missingArgTypes = 
          map snd (filter ((== (VarOrCall "?")) . fst) $ 
                   zip withMissingArgs (map declType featArgs))
        agentArgTypes = TupleType (Left missingArgTypes)
        agentType = case featureResult feat of
          NoType -> ClassType "ROUTINE" [anyType, agentArgTypes]
          t -> ClassType "FUNCTION" [anyType, agentArgTypes, t]
      in tagPos (T.Agent trg name args' agentType)

expr (ManifestCast t e) = do
  e' <- typeOfExpr e
  tagPos (T.Cast t e')

expr t = throwError ("TypeCheck.Expr.expr: " ++ show t)

-- | A call is valid if its arguments all typecheck and conform to the
-- formals, and the name exists in the class.
-- validCall :: Typ -> Typ -> String -> [Expr] -> TypingBody body ()
validCall staticType dynamicType clas fName args = 
  join (argsConform <$> argTypes <*> formTypes)
    where instFDecl = fName `inClass` staticType
          formTypes = formalArgTypes dynamicType clas =<< instFDecl
          argTypes  = mapM typeOfExpr args

-- | Takes an expression and a feature name, possibly returning
-- the expression casted to the parent which contains the feature.
-- castTargetM :: TExpr                    -- ^ The target expression
--                -> String                -- ^ Feature to search for
--                -> TypingBody body (Maybe TExpr)  -- ^ Possibly casted target
-- castTargetM trg fname = do
--   castMb <- castTargetWithName (T.texpr trg) fname
--   return (castMb >>= \cast -> return (cast trg))

-- | Cast the target based on if the name exists in the class or parent class.
-- castTargetWithName t name = castTargetWith t (isJust . flip findFeatureEx name)
    
-- castTargetWith t pr = do
--   lineageMb <- lineageWith t pr
--   p <- currentPos
--   case lineageMb of
--     Nothing -> return Nothing
--     Just lineage -> return $ Just $ lineageToCast p lineage


-- lineageToCast :: SourcePos -> [AbsClas body expr] -> TExpr -> TExpr
-- lineageToCast p [c] 
--   | className c == "ANY" = attachPos p . T.Cast (classToType c)
--   | otherwise = id
-- lineageToCast p lineage = foldl go id lineage
--   where go cast clas = attachPos p . T.Cast (classToType clas) . cast

-- lineageToName t name = lineageWith t (isJust . flip findFeatureEx name)

-- | Get the type of the parent class with the name
-- parentWithName t name = do
--   castMb <- castTargetWithName t name
--   let p0 = attachEmptyPos
--   return $ case castMb of
--     Just cast -> Just (T.texpr (cast (p0 $ T.Cast t $ p0 $ T.LitInt 0)))
--     Nothing -> Nothing

-- | Goes up the list of parents to find where a feature comes
-- from, and may produce a function that will take an expression of the 
-- target type to the parent that contains the desired feature.
--
-- This is used to both determine if a feature is available in a class,
-- and if so to return the cast to the parent class that contains it. The
-- cast is useful for code generation.
-- lineageWith :: 
--   Typ                                -- ^ The target type
--   -> (AbsClas ctxBody Expr -> Bool)  -- ^ The search predicate
--   -> TypingBody ctxBody (Maybe [AbsClas ctxBody Expr]) -- ^ The new cast
-- lineageWith t pr = 
--   let
--     go lineage parentClause = do
--       clas' <- rewriteGeneric t parentClause
--       let lin' = clas' : lineage
--       if pr clas'
--         then return (Just lin')
--         else do castsMb <- mapM (go lin') (allInherited clas')
--                 return (listToMaybe $ catMaybes castsMb)

--   in do castMb <- go [] (InheritClause t [] [] [] [] [])
--         case castMb of
--           Just xs -> return (Just $ reverse xs)
--           Nothing ->
--             do anyC <- rewriteGeneric t (InheritClause anyType [] [] [] [] [])
--                if pr anyC
--                  then return $ Just [anyC]
--                  else return $ Nothing

-- | Checks that a list of args conform to a list of types. Raises an error
-- if the check fails.
argsConform :: [TExpr]       -- ^ List of typed expressions
               -> [Typ]      -- ^ List of types that the argument list should
                             --   conform to.
               -> TypingBody body ()
argsConform args formArgs
    | length args /= length formArgs = throwError "Differing number of args"
    | otherwise = zipWithM_ conformThrow args formArgs

castGenericArgsM staticType dynamicType clas fname args =
  zipWith castToStatic args <$> 
      (formalArgDecls dynamicType clas =<< fname `inClass` staticType)

castToStatic :: TExpr -> Decl -> TExpr
castToStatic te (Decl _ t@(ClassType _ _))
    | tt == t    = te
    | isBasic tt = inheritPos (T.Box t) te
    | otherwise  = inheritPos (T.Cast t) te
    where
      tt = T.texpr te
castToStatic te _ = te



-- formalArgTypes :: Typ -> FeatureEx -> TypingBody ctxBody [Typ]
formalArgTypes dynamicType clas = 
  mapM (return . declType) <=< formalArgDecls dynamicType clas

-- formalArgDecls :: Typ -> FeatureEx -> TypingBody ctxBody [Decl]
formalArgDecls dynamicType clas = unlikeDecls dynamicType clas . featureArgs


-- unlikeDecls :: Typ -> [Decl] -> TypingBody ctxBody [Decl]
unlikeDecls clsType clas decls = 
  local (addDecls noLikes) (mapM (unlike clsType clas) decls)
    where isLike (Like _) = True
          isLike _        = False
          (likes, noLikes) = span (isLike . declType) decls



unlikeClass = unlikeAbsClass unlikeBody
unlikeInterface = unlikeAbsClass (\ _ _ x -> return x)

unlikeAbsClass unlikeImpl clas =
  classMapAttributesM unlikeAttr clas >>= classMapRoutinesM unlikeRoutine
  where
    clsType = clasToType clas
    unlike' = unlike clsType clas
    unlikeAttr a = do
      dcls <- unlike' (attrDecl a)
      return (a { attrDecl = dcls})
    unlikeRoutine r = do
      args <- unlikeDecls clsType clas (routineArgs r)
      impl <- unlikeImpl clsType clas (routineImpl r)
      Decl _ res  <- local (addDecls args) 
                           (unlike' (Decl "__unlikeRoutine" $ routineResult r))
      return (r { routineArgs = args
                , routineImpl = impl
                , routineResult = res
                })

unlikeBody typ clas (RoutineBody locals procs body) = 
  RoutineBody <$> mapM (unlike typ clas) locals <*> pure procs <*> pure body
unlikeBody _ _ b = return b
                      
clasToType cls = 
  let genType = flip ClassType [] . genericName
  in ClassType (className cls) (map genType $ generics cls)


-- | Goes up the list of parents to find where a feature comes
-- from, and may produce a function that will take an expression of the 
-- target type to the parent that contains the desired feature.
--
-- This is used to both determine if a feature is available in a class,
-- and if so to return the cast to the parent class that contains it. The
-- cast is useful for code generation.
flatten :: 
  Typ -> -- ^ Type to flatten
  TypingBody ctxBody (AbsClas ctxBody Expr) -- ^ Flattened class
flatten typ  = 
  let
    inheritType t = InheritClause t [] [] [] [] []
    
    go parentClause = do
      clas <- rewriteWithInherit parentClause
      let ihts = trace' (show (inheritClass parentClause, map inheritClass $ allInherited clas)) 
                       (allInherited clas)
      mergeClasses <$> (clas:) <$> mapM go ihts
  in do
    curr <- current <$> ask
    -- we should get the real type, but to do that we may have to unroll
    -- the 'like' parameters, which are defined on currrent.
    -- therefore we have to flatten current! to prevent infinite recursion,
    -- we test if the type we're after is current, if so we take that as 
    -- the final type
    typ' <- if typ == curr
            then return typ 
            else do currFlat <- flatten curr
                    unlikeType curr currFlat typ
    flatMb <- getFlat typ'
    case flatMb of
      Nothing -> do
        clas' <- trace' "Flatten!!!" (go (inheritType typ'))
        clasWithAny <- go (inheritType anyType)
        let clas'' = updateGeneric (Like "Current") typ' (mergeClass clas' clasWithAny)
        final <- unlikeInterface clas''
        addFlat typ' final
        return final
      Just flat -> return flat
    
    
    
trace' s e
  | False = trace s e
  | otherwise = e

-- |Rewrites a inherited class. This performs renaming and generic
-- instantiation, including "like Current" transformation.
rewriteWithInherit :: InheritClause ->
                      TypingBody ctxBody (AbsClas ctxBody Expr)
rewriteWithInherit inherit = 
  case inheritClass inherit of
    typ@(ClassType name gens) -> do
      cls <- lookupClass typ
      let update =
            updateGenerics gens . 
            undefineAll inherit .
            renameAll (rename inherit)
        -- updateGeneric (Like "Current") current .
        -- 
          
          cls' = update cls
      return cls'
    TupleType _ -> do
      cls <- lookupClass (ClassType "TUPLE" [])
      let update =
            updateGenerics [] . 
            undefineAll inherit .
            renameAll (rename inherit)
        -- updateGeneric (Like "Current") current .
        -- 
          
          cls' = update cls
      return cls'

    t -> error $ "rewriteWithInherit: " ++ show (t, inherit)
  -- unlikeInterface cls'
  -- if name == "ARRAY" && gens == [ClassType "K" []]
  --   then trace (show 
  --               (map (\fex -> (featureName fex, featureArgs fex, featureResult fex)) (allRoutines cls')) ++ show (generics cls, generics cls', typ, current)) (return cls')
  --   else return cls'
