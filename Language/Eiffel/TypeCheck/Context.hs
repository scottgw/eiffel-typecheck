{-# LANGUAGE TypeSynonymInstances, MultiParamTypeClasses, FlexibleInstances #-}

module Language.Eiffel.TypeCheck.Context where

import Control.Monad.Error
import Control.Monad.Identity
import Control.Monad.Reader

import Data.Map hiding (map, null)
import Prelude hiding (lookup)

import Language.Eiffel.Eiffel

import qualified Language.Eiffel.TypeCheck.TypedExpr as T
import Language.Eiffel.TypeCheck.TypedExpr (TExpr)

import Util.Monad

data TypeContext = TypeContext {
      interfaces :: Map ClassName ClasInterface,
      current    :: Clas,
      result     :: Typ,
      variables  :: Map String Typ,
      pos        :: SourcePos
    }

type TypeError = ErrorT String Identity
type Typing = ReaderT TypeContext TypeError

instance HasClasEnv TypeContext where
    classEnv = interfaces
    update tc c = tc {interfaces = insert (className c) c (interfaces tc)}
instance ClassReader TypeContext Typing

currentPos :: Typing SourcePos
currentPos = pos `fmap` ask

tagPos :: a -> Typing (Pos a)
tagPos a = currentPos >>= return . flip attachPos a

setPosition :: SourcePos -> Typing a -> Typing a
setPosition p = local (\ c -> c {pos = p})

idErrorRead :: Typing a -> TypeContext -> Either String a
idErrorRead m = runIdentity . runErrorT . runReaderT m

guardThrow :: Bool -> String -> Typing ()
guardThrow False = throwErrorPos
guardThrow True  = const (return ())

maybeThrow :: Maybe a -> String -> Typing a
maybeThrow (Just v) = const (return v)
maybeThrow Nothing  = throwErrorPos

throwErrorPos :: String -> Typing a
throwErrorPos e = do
  p <- currentPos
  throwError (e ++ " @ " ++ show p)

currentM :: Typing TExpr
currentM = do
  cur <- current `fmap` ask
  let cname = className cur
  let gs = map (flip ClassType [] . genericName) (generics cur)
  tagPos (T.CurrentVar $ ClassType cname gs)

mkCtx :: Clas -> [ClasInterface] -> TypeContext
mkCtx c cs = 
    TypeContext 
    {
      interfaces = clasMap cs
    , current = c 
    , result = error "mkCtx: no Result"
    , variables = empty -- attrMap c
    , pos = error "mkCtx: no position"
    }

varCtx :: Typing (Map String Typ)
varCtx = fmap variables ask

typeOfVar :: String -> Typing (Maybe Typ)
typeOfVar "Result" = (Just . result) `fmap` ask
typeOfVar str = lookup str `fmap` varCtx 

typeOfVar' :: String -> Typing Typ
typeOfVar' str 
    = do mV <- typeOfVar str
         m <- varCtx
         case mV of
           Just v -> return v
           Nothing -> 
               throwErrorPos (concat ["Variable not found: ", str, ".", show m])

addDeclsToMap :: [Decl] -> Map String Typ -> Map String Typ
addDeclsToMap = union . declsToMap

addDecls :: [Decl] -> TypeContext -> TypeContext
addDecls ds ctx = ctx {variables = addDeclsToMap ds (variables ctx)}

setResult :: Routine -> TypeContext -> TypeContext
setResult f tc = tc {result = featureResult f}
