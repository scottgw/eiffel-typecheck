{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Eiffel.TypeCheck.Expr 
       (typeOfExpr, typeOfExprIs, clause, unlikeDecls) where

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

clause :: Clause Expr -> TypingBody body (Clause TExpr)
clause (Clause n e) =
  Clause n <$> typeOfExprIs boolType e

-- | Determine whether a given string (for a VarOrCall) is a call or
-- a local variable of some sort.
convertVarCall :: String -> TypingBody body (Maybe TExpr)
convertVarCall name = do
  current <- currentM
  trgM <- castTargetM current name
  case trgM of
    Nothing -> 
      do vTyp <- typeOfVar name
         maybeTag (T.Var name <$> vTyp)
    Just trg' -> Just <$> expr (UnqualCall name []) -- compCall trg' name

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

expr :: UnPosExpr -> TypingBody body TExpr
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
  unlikedRes <- unlikeType curr res
  tagPos (T.ResultVar unlikedRes)
expr (StaticCall typ name args) = do
  parentMb <- parentWithName typ name
  case parentMb of
    Nothing -> 
      throwError (show typ ++ ": does not contain static call " ++ name)
    Just typ' -> do 
      args' <- mapM typeOfExpr args
      cls <- lookupClass typ'
      let 
        f = fromMaybe (error $ "TypeCheck.Expr.expr: StaticCall " ++ name ++ ":" ++ show typ') 
                      (findFeatureEx cls name)
        argTypes = map declType (featureArgs f)
      argsConform args' argTypes
      tagPos (T.StaticCall typ' name args' (featureResult f))
                   
expr (VarOrCall s) = do
  exprMb <- convertVarCall s
  c <- currentM
  maybe (throwError ("TypeCheckc.Expr.expr: Can't resolve " ++ s ++ " from " ++ show c)) return exprMb
expr (Attached typeMb attch asMb) = do
  --TODO: Decide if we have to do any checking between typeMb and attch
  attch' <- typeOfExpr attch
  tagPos $ T.Attached typeMb attch' asMb

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
    let extraLocals = \ m -> 
          case contents e1' of
            T.Attached _typeMb attch asMb ->
              let attTyp = T.texpr attch
              in case asMb of 
                Just as -> do curr <- current `fmap` ask
                              dcl <- unlike curr (Decl as attTyp)
                              local (addDecls [dcl]) m
                Nothing -> m
            _ -> m
    castMb <- castTargetWith (T.texpr e1') 
                             (\c -> isJust $ findOperator c (opAlias op) 1)
    case castMb of
      Nothing -> throwError ("No feature found associated with operator " ++ show op ++ " in " ++ show (T.texpr e1'))
      Just cast -> do
        let t = T.texpr (cast e1')
        cls <- lookupClass t
        let f = fromMaybe (error "TypeCheck.Expr.expr: BinOpExpr") (findOperator cls (opAlias op) 1)
        extraLocals (expr $ QualCall e1 (featureName f) [e2])

expr (UnqualCall fName args) = do
  qual <- QualCall <$> tagPos CurrentVar 
                   <*> pure fName 
                   <*> pure args
  expr qual
  
expr (QualCall trg name args) = do 
  -- typecheck and cast the target if from a generic class
  trg' <- typeOfExpr trg
  args' <- mapM typeOfExpr args
  
  Just lineage <- lineageToName (T.texpr trg') name
  -- if name == "twin" then error "twin!" else return ()
  case findFeatureEx (last lineage) name of
    Nothing -> error $ show trg' ++ ": " ++ name ++ show args'
    Just feat -> do
      let formArgs = map declType (featureArgs feat)
          res = featureResult feat
      argsConform args' formArgs
      tagPos (T.Call trg' name args' res)
  -- tTrg        <- castTarget trgUncasted fName
  
  -- let staticType = T.texpr tTrg
  --     dynamicType = T.texpr trgUncasted
  
  
  -- -- See if this qualified call is actually a class access, and
  -- -- either cast it to an access if it is one, or just return the
  -- -- fully casted call AST if it's really a call
  -- accessMb <- compCall tTrg fName
  -- case accessMb of
  --   Just acc -> castAccess acc
  --   Nothing  -> do 
  --     -- see if the call is valid wth the args proposed
  --     validCall staticType dynamicType fName args
  
  --     -- typecheck and cast the arguments if they come from a generic class
  --     args' <- mapM typeOfExpr args
  --     genArgs <- castGenericArgsM staticType dynamicType fName args'

  --     -- fetch the actual result, make a new call from it,
  --     -- then cast the result if necessary
  --     resultT <- featureResult <$> (fName `inClass` staticType)
      
  --     tCall <- tagPos (T.Call tTrg fName genArgs resultT)
  --     castResult staticType dynamicType fName tCall
expr (CreateExpr typ name args) = do
  -- this comes basically from the above 
  -- see if the call is valid wth the args proposed
  typMb <- parentWithName typ name
  typ' <- maybe (throwError $ "create expression: can't find " ++ name)
                return typMb
  
  validCall typ' typ name args
  
  -- typecheck and cast the arguments if they come from a generic class
  args'   <- mapM typeOfExpr args
  genArgs <- castGenericArgsM typ' typ name args'

  tagPos (T.CreateExpr typ name genArgs)
expr (LitType t) = tagPos (T.LitType t)
expr t = throwError ("TypeCheck.Expr.expr: " ++ show t)

-- | A call is valid if its arguments all typecheck and conform to the
-- formals, and the name exists in the class.
validCall :: Typ -> Typ -> String -> [Expr] -> TypingBody body ()
validCall staticType dynamicType fName args = 
  join (argsConform <$> argTypes <*> formTypes)
    where instFDecl = fName `inClass` staticType
          formTypes = formalArgTypes dynamicType =<< instFDecl
          argTypes  = mapM typeOfExpr args

-- | Takes an expression and a feature name, possibly returning
-- the expression casted to the parent which contains the feature.
castTargetM :: TExpr                    -- ^ The target expression
               -> String                -- ^ Feature to search for
               -> TypingBody body (Maybe TExpr)  -- ^ Possibly casted target
castTargetM trg fname = do
  castMb <- castTargetWithName (T.texpr trg) fname
  return (castMb >>= \cast -> return (cast trg))

-- | Cast the target based on if the name exists in the class or parent class.
castTargetWithName t name = castTargetWith t (isJust . flip findFeatureEx name)
    
castTargetWith t pr = do
  lineageMb <- lineageWith t pr
  p <- currentPos
  case lineageMb of
    Nothing -> return Nothing
    Just lineage -> return $ Just $ lineageToCast p lineage


lineageToCast :: SourcePos -> [AbsClas body expr] -> TExpr -> TExpr
lineageToCast p [c] 
  | className c == "ANY" = attachPos p . T.Cast (classToType c)
  | otherwise = id
lineageToCast p lineage = foldl go id lineage
  where go cast clas = attachPos p . T.Cast (classToType clas) . cast

lineageToName t name = lineageWith t (isJust . flip findFeatureEx name)

-- | Get the type of the parent class with the name
parentWithName t name = do
  castMb <- castTargetWithName t name
  let p0 = attachEmptyPos
  return $ case castMb of
    Just cast -> Just (T.texpr (cast (p0 $ T.Cast t $ p0 $ T.LitInt 0)))
    Nothing -> Nothing

-- | Goes up the list of parents to find where a feature comes
-- from, and may produce a function that will take an expression of the 
-- target type to the parent that contains the desired feature.
--
-- This is used to both determine if a feature is available in a class,
-- and if so to return the cast to the parent class that contains it. The
-- cast is useful for code generation.
lineageWith :: 
  Typ                                -- ^ The target type
  -> (AbsClas ctxBody Expr -> Bool)  -- ^ The search predicate
  -> TypingBody ctxBody (Maybe [AbsClas ctxBody Expr]) -- ^ The new cast
lineageWith t pr = 
  let
    anyT = ClassType "ANY" []

    go parentClause lineage = do
      clas' <- rewriteGeneric t parentClause
      let lin' = clas' : lineage
      if pr clas'
        then return (Just lin')
        else do castsMb <- mapM (flip go lin') (allInherited clas')
                return (listToMaybe $ catMaybes castsMb)

  in do castMb <- go (InheritClause t [] [] [] [] []) []
        case castMb of
          Just xs -> return (Just $ reverse xs)
          Nothing ->
            do anyC <- rewriteGeneric t (InheritClause anyT [] [] [] [] [])
               if pr anyC
                 then return $ Just [anyC]
                 else return $ Nothing

-- | Checks that a list of args conform to a list of types. Raises an error
-- if the check fails.
argsConform :: [TExpr]       -- ^ List of typed expressions
               -> [Typ]      -- ^ List of types that the argument list should
                             --   conform to.
               -> TypingBody body ()
argsConform args formArgs
    | length args /= length formArgs = throwError "Differing number of args"
    | otherwise = zipWithM_ conformThrow args formArgs

castGenericArgsM :: Typ -> Typ -> String -> [TExpr] -> TypingBody body [TExpr]
castGenericArgsM staticType dynamicType fname args =
  zipWith castToStatic args <$> 
      (formalArgDecls dynamicType =<< fname `inClass` staticType)

castToStatic :: TExpr -> Decl -> TExpr
castToStatic te (Decl _ t@(ClassType _ _))
    | tt == t    = te
    | isBasic tt = inheritPos (T.Box t) te
    | otherwise  = inheritPos (T.Cast t) te
    where
      tt = T.texpr te
castToStatic te _ = te



formalArgTypes :: Typ -> FeatureEx -> TypingBody ctxBody [Typ]
formalArgTypes dynamicType = 
  mapM (return . declType) <=< formalArgDecls dynamicType

formalArgDecls :: Typ -> FeatureEx -> TypingBody ctxBody [Decl]
formalArgDecls dynamicType = unlikeDecls dynamicType . featureArgs


unlikeDecls :: Typ -> [Decl] -> TypingBody ctxBody [Decl]
unlikeDecls clsType decls = 
  local (addDecls noLikes) (mapM (unlike clsType) decls)
    where isLike (Like _) = True
          isLike _        = False
          (likes, noLikes) = span (isLike . declType) decls



-- |Rewrites a inherited class. This performs renaming and generic
-- instantiation, including "like Current" transformation.
rewriteGeneric :: Typ -> InheritClause ->
                  TypingBody ctxBody (AbsClas ctxBody Expr)
rewriteGeneric current inherit = do
  let typ@(ClassType name gens) = inheritClass inherit
  cls <- lookupClass typ
  let update = 
        renameAll (rename inherit) .
        updateGeneric (Like "Current") current . 
        updateGenerics gens
  return (update cls)