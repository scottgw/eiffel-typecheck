{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}

module Util.Monad where

import Control.Applicative
import Control.Monad.Reader

import Data.Map

import Language.Eiffel.Syntax
import Language.Eiffel.Util

class HasClasEnv r body | r -> body where
    classEnv :: r -> Map String (AbsClas body Expr)
    update   :: r -> (AbsClas body Expr) -> r

class (HasClasEnv r body, MonadReader r m) => 
      ClassReader r m body | m -> r where

askClassEnv :: ClassReader r m body => m (Map String (AbsClas body Expr))
askClassEnv = classEnv `liftM` ask

lookupClassM :: ClassReader r m body => 
                Typ -> m (Maybe (AbsClas body Expr))
lookupClassM (ClassType cn _) = Data.Map.lookup cn `liftM` askClassEnv
lookupClassM (Sep _ _ cn)     = lookupClassM (ClassType cn [])
lookupClassM t = error $ "lookupClassM: can't lookup a " ++ show t ++ " type"

lookupClass :: ClassReader r m body => Typ -> m (AbsClas body Expr)
lookupClass t = liftM (maybe (error $ "lookupClas: can't find " ++ show t) id) 
                (lookupClassM t)


lookupFeatureM typ name = do
  clas <- lookupClassM typ
  return (findFeature <$> clas <*> pure name)

lookupAttrM :: ClassReader r m body => Typ -> String 
               -> m (Maybe (Attribute Expr))
lookupAttrM t name = do
  c <- lookupClassM t
  return (do
           c' <- c
           findAttrInt c' name)

lookupAttr :: ClassReader r m body => Typ -> String -> m (Attribute Expr)
lookupAttr t name 
    = liftM (maybe 
             (error $ "lookupAttr: can't fine " ++ show t ++ "." ++ name)
             id)
      (lookupAttrM t name)


-- lookupRoutineM :: ClassReader r m body => Typ -> String -> m (Maybe RoutineI)
lookupRoutineM t name = do
  c <- lookupClassM t
  return (do
           c' <- c
           findRoutineInt c' name)

-- lookupRoutine :: ClassReader r m body => Typ -> String -> m RoutineI
lookupRoutine t name 
    = liftM (maybe 
             (error $ "lookupRoutine: can't fine " ++ show t ++ "." ++ name)
             id)
      (lookupRoutineM t name)
            