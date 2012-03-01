{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Eiffel.TypeCheck.Expr where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.Reader

import Data.Maybe

import Language.Eiffel.Eiffel

import qualified Language.Eiffel.TypeCheck.TypedExpr as T
import Language.Eiffel.TypeCheck.TypedExpr (TExpr)
import Language.Eiffel.TypeCheck.BasicTypes
import Language.Eiffel.TypeCheck.Context
import Language.Eiffel.TypeCheck.Generic

import Util.Monad

clause :: Clause Expr -> Typing (Clause TExpr)
clause (Clause n e) =
  Clause n <$> typeOfExprIs BoolType e

convertVarCall :: String -> TExpr -> Typing (Maybe TExpr)
convertVarCall vc trg = do
  trgM <- castTargetM trg vc
  p <- currentPos
  case trgM of
    Nothing -> 
      do vTyp <- typeOfVar vc
         return (attachPos p <$> (T.Var vc <$> vTyp))
    Just trg' -> compCall vc trg' p <$> resolveIFace (T.texpr trg')
           

compCall :: String -> TExpr -> SourcePos -> ClasInterface -> Maybe TExpr
compCall vc trg p ci = 
    attachPos p <$> (asAccess trg ci vc <|> 
                     asCall trg ci vc)

-- | Possibly construct a target/name pair as attribute-access.
asAccess :: TExpr -> ClasInterface -> String -> Maybe T.UnPosTExpr
asAccess trg ci vc = 
    let dec = attrDecl <$> findAttrInt ci vc
    in T.Access trg <$> (declName <$> dec) 
                    <*> (declType <$> dec)

-- | Possibly construct a target/name pair as a call (with no arguments)
asCall :: TExpr -> ClasInterface -> String -> Maybe T.UnPosTExpr
asCall trg ci vc = do 
  f <- findRoutineInt ci vc
  guard (null (routineArgs f))
  return (T.Call trg (featureName f) [] (featureResult f))

typeOfExpr :: Expr -> Typing TExpr
typeOfExpr e = setPosition (position e) (expr (contents e))

typeOfExprIs :: Typ -> Expr -> Typing TExpr
typeOfExprIs typ expr = do
  e' <- typeOfExpr expr
  _  <- guardTypeIs typ e'
  return e'


binOpArgCasts e1 e2 
  | isBasic t1 && isBasic t2 = return (e1,e2)
  | otherwise = 
    do cast1M <- conforms t1 t2
       cast2M <- conforms t2 t1
       
       -- if one type can be casted to another, then apply the first
       -- cast that's possible.
       let tupMb = (cast1M >>= \ c -> return (c e1, e2)) <|> 
                   (cast2M >>= \ c -> return (e1, c e2))
       
       -- return the tuple with the proper cast, or throw an error
       -- if neither are possible
       maybe (throwError $ "binOpArgCasts: " ++ show (e1,e2)) return tupMb
    where 
      t1 =  T.texprTyp (contents e1)
      t2 =  T.texprTyp (contents e2)
                                       

expr :: UnPosExpr -> Typing TExpr
expr (LitInt i)    = tagPos (T.LitInt i)
expr (LitDouble d) = tagPos (T.LitDouble d)
expr (LitBool b)   = tagPos (T.LitBool b)
expr LitVoid       = tagPos (T.LitVoid VoidType)
expr (LitString s) = tagPos (T.LitString s)
expr (LitChar c)   = tagPos (T.LitChar c)
expr CurrentVar    = currentM
expr ResultVar     = (T.ResultVar <$> result <$> ask) >>= tagPos

expr (VarOrCall s) = (convertVarCall s =<< currentM) >>=
    maybe (throwError ("Can't resolve " ++ s)) return

expr (UnOpExpr op e) = tagPos =<< (T.UnOpExpr op <$> te <*> res)
  where te  = typeOfExpr e
        res = unOpTypes op =<< (T.texpr <$> te)
        
expr (BinOpExpr (SymbolOp op) e1 e2) = do
  e1' <- typeOfExpr e1
  cls <- lookupClass (T.texpr e1')
  case findOperator cls op of
    Nothing -> throwError ("No feature found associated with operator " ++ op)
    Just f -> expr (QualCall e1 (featureName f) [e2])
    
expr (BinOpExpr op e1 e2) = do
  e1' <- typeOfExpr e1
  e2' <- typeOfExpr e2
  (e1'', e2'') <- binOpArgCasts e1' e2'
  (resType, argType) <- opTypes op (T.texpr e1'') (T.texpr e2'')
  tagPos $ T.BinOpExpr 
         (castOp op argType)
         (castTyp argType e1'')
         (castTyp argType e2'')
         resType
         
expr (UnqualCall fName args) = do
  qual <- QualCall <$> tagPos CurrentVar 
                   <*> pure fName 
                   <*> pure args
  expr qual
  
expr (QualCall trg fName args) = do 
  -- typecheck and cast the target if from a generic class
  p <- currentPos
  trgUncasted <- typeOfExpr trg
  tTrg        <- castTarget trgUncasted fName
  let t = T.texpr tTrg
  
  -- See if this qualified call is actually a class access, and
  -- either cast it to an access if it is one, or just return the
  -- fully casted call AST if it's really a call
  accessMb <- compCall fName tTrg p <$> resolveIFace (T.texpr tTrg)
  case accessMb of
    Just acc -> castAccess acc
    Nothing  -> do 
      -- see if the call is valid wth the args proposed
      validCall t fName args
  
      -- typecheck and cast the arguments if they come from a generic class
      args'   <- mapM typeOfExpr args
      genArgs <- castGenericArgsM t fName args'
  
      -- fetch the actual result, make a new call from it,
      -- then cast the result if necessary
      resultT <- featureResult <$> (fName `inClass` t :: Typing FeatureEx)
      tCall <- tagPos (T.Call tTrg fName genArgs resultT)
      castResult t fName tCall
  

expr (Cast t e) = T.Cast t `fmap` typeOfExpr e >>= tagPos


-- | A call is valid if its arguments all typecheck and conform to the
-- formals, and the name exists in the class.
validCall :: Typ -> String -> [Expr] -> Typing ()
validCall t fName args = join (argsConform <$> argTypes <*> formTypes)
    where instFDecl = fName `inClass` t
          formTypes = formalArgTypes <$> instFDecl
          argTypes  = mapM typeOfExpr args

-- | Casts the target expression to the parent which contains the feature name.
-- Throws an exception if no parents contain the feature name.
castTarget :: TExpr            -- ^ The target expression
               -> String       -- ^ Feature to search for
               -> Typing TExpr -- ^ Casted target
castTarget trg fname = do
  castTrgMb <- castTargetM trg fname
  maybe (throwError $ "castTarget error " ++ show (trg, fname)) return castTrgMb

-- | Takes an expression and a feature name, possibly returning
-- the expression casted to the parent which contains the feature.
castTargetM :: TExpr                    -- ^ The target expression
               -> String                -- ^ Feature to search for
               -> Typing (Maybe TExpr)  -- ^ Possibly casted target
castTargetM trg fname = do
  castMb <- castTargetWith (T.texpr trg) fname id
  return (castMb >>= \cast -> return (cast trg))

-- | Goes up the list of parents to find where a feature comes
-- from, and may produce a function that will take an expression of the 
-- target type to the parent that contains the desired feature.
--
-- This is used to both determine if a feature is available in a class,
-- and if so to return the cast to the parent class that contains it. The
-- cast is useful for code generation.
castTargetWith :: Typ                  -- ^ The target type
                  -> String            -- ^ The feature name
                  -> (TExpr -> TExpr)  -- ^ The cast so far
                  -> Typing (Maybe (TExpr -> TExpr)) -- ^ The new cast
castTargetWith t fname cast = do
  ci <- lookupClass t
  if isJust (findFeatureEx ci fname)
    then return (Just cast)
    else do
      let inheritCast parent = 
            castTargetWith parent fname (inheritPos (T.Cast parent) . cast)
      castsMb <- mapM inheritCast (map inheritClass (inherit ci))
      return (listToMaybe $ catMaybes castsMb)

-- | If the target expr is an attribute access then lookup then possibly
-- cast or unbox the result in the case where the originating class is generic.
castAccess :: TExpr -> Typing TExpr
castAccess a = case contents a of
                 T.Access ta aName _ -> castAttr (T.texpr ta) aName a
                 _ -> return a

formalArgTypes :: RoutineI -> [Typ]
formalArgTypes = map declType . routineArgs

-- | Checks that a list of args conform to a list of types. Raises an error
-- if the check fails.
argsConform :: [TExpr]       -- ^ List of typed expressions
               -> [Typ]      -- ^ List of types that the argument list should
                             --   conform to.
               -> Typing ()
argsConform args formArgs
    | length args /= length formArgs = throwError "Differing number of args"
    | otherwise = zipWithM_ conformThrow args formArgs

-- | Casts the return value of a function. If the yare the same,
-- there's no cast, but if one is a generic
castReturnedValue :: Typ      -- ^ Instantiated type
                     -> Typ   -- ^ Generic type
                     -> TExpr -- ^ Expression of instantiated type
                     -> TExpr -- ^ Possibly casted or boxed expression.
castReturnedValue instanceTyp genericTyp
    | instanceTyp == genericTyp  = id
    | isBasic instanceTyp        = inheritPos (T.Unbox instanceTyp)
    | otherwise                  = inheritPos (T.Cast instanceTyp)


-- | Casts the result of an attribute lookup, if necessary.
-- This assumes that the 
castAttr :: Typ -> String -> TExpr -> Typing TExpr
castAttr = castFeatureResult (declType . attrDecl)

castResult :: Typ -> String -> TExpr -> Typing TExpr
castResult = castFeatureResult routineResult

castFeatureResult :: ClassFeature a EmptyBody Expr =>
                     (a -> Typ) -> 
                     Typ -> String -> TExpr -> Typing TExpr
castFeatureResult res targetType featureName expr =
  castReturnedValue <$> (res <$> inClass featureName targetType)
                    <*> (res <$> inGenClass featureName targetType)
                    <*> pure expr
  


castGenericArgsM :: Typ -> String -> [TExpr] -> Typing [TExpr]
castGenericArgsM t fname args =
  zipWith castToStatic args <$> routineArgs <$> fname `inClass` t

castToStatic :: TExpr -> Decl -> TExpr
castToStatic te (Decl _ t@(ClassType _ _))
    | tt == t    = te
    | isBasic tt = inheritPos (T.Box t) te
    | otherwise  = inheritPos (T.Cast t) te
    where
      tt = T.texpr te
castToStatic te _ = te
