{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}

module Util.Monad where

import Control.Applicative
import Control.Monad.Reader

import Data.Map

import Language.Eiffel.Class
import Language.Eiffel.Expr
import Language.Eiffel.Feature
import Language.Eiffel.Typ
import Language.Eiffel.Decl

class HasClasEnv r where
    classEnv :: r -> Map String ClasInterface
    update   :: r -> ClasInterface -> r

class (HasClasEnv r, MonadReader r m) => ClassReader r m | m -> r where

askClassEnv :: ClassReader r m => m (Map String ClasInterface)
askClassEnv = classEnv `liftM` ask

lookupClassM :: ClassReader r m => Typ -> m (Maybe ClasInterface)
lookupClassM (ClassType cn _) = Data.Map.lookup cn `liftM` askClassEnv
lookupClassM (Sep _ _ cn)     = lookupClassM (ClassType cn [])
lookupClassM t = error $ "lookupClassM: can't lookup a " ++ show t ++ " type"

lookupClass :: ClassReader r m => Typ -> m ClasInterface
lookupClass t = liftM (maybe (error $ "lookupClas: can't find " ++ show t) id) 
                (lookupClassM t)


lookupFeatureM typ name = do
  clas <- lookupClassM typ
  return (findFeatureInt <$> clas <*> pure name)

lookupAttrM :: ClassReader r m => Typ -> String -> m (Maybe (Attribute Expr))
lookupAttrM t name = do
  c <- lookupClassM t
  return (do
           c' <- c
           findAttrInt c' name)

lookupAttr :: ClassReader r m => Typ -> String -> m (Attribute Expr)
lookupAttr t name 
    = liftM (maybe 
             (error $ "lookupAttr: can't fine " ++ show t ++ "." ++ name)
             id)
      (lookupAttrM t name)


lookupRoutineM :: ClassReader r m => Typ -> String -> m (Maybe RoutineI)
lookupRoutineM t name = do
  c <- lookupClassM t
  return (do
           c' <- c
           findRoutineInt c' name)

lookupRoutine :: ClassReader r m => Typ -> String -> m RoutineI
lookupRoutine t name 
    = liftM (maybe 
             (error $ "lookupRoutine: can't fine " ++ show t ++ "." ++ name)
             id)
      (lookupRoutineM t name)
            