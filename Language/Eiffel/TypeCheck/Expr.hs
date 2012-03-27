{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Language.Eiffel.TypeCheck.Expr 
       (typeOfExpr, typeOfExprIs, clause, unlikeDecls, flatten) where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.Reader

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
    Just _ -> Just <$> expr (UnqualCall name [])

maybeTag :: Maybe a -> TypingBody ctxBody (Maybe (Pos a))
maybeTag Nothing  = return Nothing
maybeTag (Just x) = Just <$> tagPos x

typeOfExpr :: Expr -> TypingBody body TExpr
typeOfExpr e = setPosition (position e) 
               (catchError (expr (contents e))
                           (\str -> throwError $ 
                                    str ++ " at " ++ show (position e)))

typeOfExprIs :: Typ -> Expr -> TypingBody body TExpr
typeOfExprIs typ e = do
  e' <- typeOfExpr e
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
    e1' <- typeOfExpr e1

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
  flatCls  <- flatten targetType
  
  case findFeatureEx flatCls name of
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
                 arg' <- tagPos (T.Cast targetType arg)
                 tagPos (T.Call trg' name [arg'] res)
               else if contents trg' `numericCanBe` T.texpr arg 
                    then do 
                      trg'' <- tagPos (T.Cast (T.texpr arg) trg')
                      tagPos (T.Call trg'' name [arg] res)
                    else throwError $ e ++ " AND! " ++ show (trg',name,args, targetType)
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
    other -> throwError $ "Unallowed agent: " ++ show other
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

-- | Checks that a list of args conform to a list of types. Raises an error
-- if the check fails.
argsConform :: [TExpr]       -- ^ List of typed expressions
               -> [Typ]      -- ^ List of types that the argument list should
                             --   conform to.
               -> TypingBody body ()
argsConform args formArgs
    | length args /= length formArgs = throwError "Differing number of args"
    | otherwise = zipWithM_ conformThrow args formArgs


-- unlikeDecls :: Typ -> [Decl] -> TypingBody ctxBody [Decl]
unlikeDecls clsType clas decls = 
  local (addDecls noLikes) (mapM (unlike clsType clas) decls)
    where isLike (Like _) = True
          isLike _        = False
          noLikes = filter (not . isLike . declType) decls



-- unlikeClass = unlikeAbsClass unlikeBody
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
      let ihts = allInherited clas
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
        clas' <- go (inheritType typ')
        clasWithAny <- go (inheritType anyType)
        let clas'' = updateGeneric (Like "Current") typ' (mergeClass clas' clasWithAny)
        final <- unlikeInterface clas''
        addFlat typ' final
        return final
      Just flat -> return flat

-- |Rewrites a inherited class. This performs renaming and generic
-- instantiation, including "like Current" transformation.
rewriteWithInherit :: InheritClause ->
                      TypingBody ctxBody (AbsClas ctxBody Expr)
rewriteWithInherit inhrt = 
  let updateWithGens gens =
        updateGenerics gens . 
        undefineAll inhrt .
        renameAll (rename inhrt)
  in case inheritClass inhrt of
    typ@(ClassType _ gens) -> do
      cls <- lookupClass typ
      return (updateWithGens gens cls)
    TupleType _ -> do
      cls <- lookupClass (ClassType "TUPLE" [])
      return (updateWithGens [] cls)
    t -> error $ "rewriteWithInherit: " ++ show (t, inhrt)
