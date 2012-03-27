{-# LANGUAGE TypeSynonymInstances, MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Eiffel.TypeCheck.Context where

import Control.Monad.Error
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State

import Data.Char
import qualified Data.Map as Map
import Data.Map (Map)

import Language.Eiffel.Syntax
import Language.Eiffel.Position
import Language.Eiffel.Util

import qualified Language.Eiffel.TypeCheck.TypedExpr as T
import Language.Eiffel.TypeCheck.TypedExpr (TExpr)

import Util.Monad

data TypeContext body = TypeContext {
      interfaces :: Map ClassName (AbsClas body Expr),
      current    :: Typ,
      result     :: Typ,
      variables  :: Map String Typ,
      pos        :: SourcePos
    }

type FlatMap body = Map Typ (AbsClas body Expr)

type TypeError = ErrorT String Identity
type FlatLookup body = StateT (FlatMap body) TypeError
type TypingBody body = ReaderT (TypeContext body) (FlatLookup body)
type Typing = TypingBody (RoutineBody Expr)

instance HasClasEnv (TypeContext body) body where
    classEnv = interfaces
    update tc c = tc {interfaces = Map.insert (className c) c (interfaces tc)}
instance ClassReader (TypeContext body) (TypingBody body) body

currentPos :: TypingBody body SourcePos
currentPos = pos `fmap` ask

tagPos :: a -> TypingBody body (Pos a)
tagPos a = currentPos >>= return . flip attachPos a

setPosition :: SourcePos -> TypingBody body a -> TypingBody body a
setPosition p = local (\ c -> c {pos = p})

idErrorRead :: TypingBody body a -> TypeContext body -> Either String a
idErrorRead ctx = 
  runIdentity . runErrorT . fmap fst . flip runStateT Map.empty . runReaderT ctx


addFlat :: Typ -> AbsClas body Expr -> TypingBody body ()
addFlat t flat = lift (modify (Map.insert t flat))

getFlat :: Typ -> TypingBody body (Maybe (AbsClas body Expr))
getFlat t = lift (gets (Map.lookup t))

guardThrow :: Bool -> String -> TypingBody body ()
guardThrow False = throwErrorPos
guardThrow True  = const (return ())

maybeThrow :: Maybe a -> String -> TypingBody body a
maybeThrow (Just v) = const (return v)
maybeThrow Nothing  = throwErrorPos

throwErrorPos :: String -> TypingBody body a
throwErrorPos e = do
  p <- currentPos
  throwError (e ++ " @ " ++ show p)

currentM :: TypingBody body TExpr
currentM = do
  t <- current `fmap` ask
  tagPos (T.CurrentVar t)

mkCtx :: Typ -> [AbsClas body Expr] -> TypeContext body
mkCtx currTyp cs = 
    TypeContext 
    { interfaces = clasMap cs
    , current = currTyp 
    , result = error "mkCtx: no Result"
    , variables = Map.empty -- attrMap c
    , pos = error "mkCtx: no position"
    }

varCtx :: TypingBody body (Map String Typ)
varCtx = fmap variables ask

typeOfVar :: String -> TypingBody body (Maybe Typ)
typeOfVar "Result" = (Just . result) `fmap` ask
typeOfVar str = Map.lookup (map toLower str) `fmap` varCtx 

typeOfVar' :: String -> TypingBody body Typ
typeOfVar' str 
    = do mV <- typeOfVar str
         m <- varCtx
         case mV of
           Just v -> return v
           Nothing -> 
               throwErrorPos (concat ["Variable not found: ", str, ".", show m])

addDeclsToMap :: [Decl] -> Map String Typ -> Map String Typ
addDeclsToMap = Map.union . declsToMap

addDecls :: [Decl] -> TypeContext body -> TypeContext body
addDecls ds ctx = ctx {variables = addDeclsToMap ds (variables ctx)}

setResult :: AbsRoutine body' Expr -> TypeContext body -> TypeContext body
setResult f tc = tc {result = featureResult f}
