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

data TypeContext body expr = TypeContext {
      interfaces :: Map ClassName (AbsClas body expr),
      current    :: Typ,
      result     :: Typ,
      variables  :: Map String Typ,
      pos        :: SourcePos
    }

type FlatMap body expr = Map Typ (AbsClas body expr)

type TypeError = ErrorT String Identity
type FlatLookup body expr = StateT (FlatMap body expr) TypeError
type TypingBodyExpr body expr = 
  ReaderT (TypeContext body expr) (FlatLookup body expr)
type TypingBody body = TypingBodyExpr body Expr
type Typing = TypingBody (RoutineBody Expr)

instance HasClasEnv (TypeContext body expr) body expr where
    classEnv = interfaces
    update tc c = tc {interfaces = Map.insert (className c) c (interfaces tc)}
instance ClassReader 
           (TypeContext body expr) 
           (TypingBodyExpr body expr) 
           body 
           expr

currentPos :: TypingBodyExpr body expr SourcePos
currentPos = pos `fmap` ask

tagPos :: a -> TypingBodyExpr body expr (Pos a)
tagPos a = currentPos >>= return . flip attachPos a

setPosition :: SourcePos -> TypingBody body a -> TypingBody body a
setPosition p = local (\ c -> c {pos = p})

idErrorRead :: TypingBodyExpr body expr a -> 
               TypeContext body expr -> Either String a
idErrorRead ctx = 
  runIdentity . runErrorT . fmap fst . flip runStateT Map.empty . runReaderT ctx


addFlat :: Typ -> AbsClas body expr -> TypingBodyExpr body expr ()
addFlat t flat = lift (modify (Map.insert t flat))

getFlat :: Typ -> TypingBodyExpr body expr (Maybe (AbsClas body expr))
getFlat t = lift (gets (Map.lookup t))

guardThrow :: Bool -> String -> TypingBody body ()
guardThrow False = throwErrorPos
guardThrow True  = const (return ())

maybeThrow :: Maybe a -> String -> TypingBody body a
maybeThrow (Just v) = const (return v)
maybeThrow Nothing  = throwErrorPos

throwErrorPos :: String -> TypingBodyExpr body expr a
throwErrorPos e = do
  p <- currentPos
  throwError (e ++ " @ " ++ show p)

currentM :: TypingBody body TExpr
currentM = do
  t <- current `fmap` ask
  tagPos (T.CurrentVar t)

mkCtx :: Typ -> [AbsClas body expr] -> TypeContext body expr
mkCtx currTyp cs = 
    TypeContext 
    { interfaces = clasMap cs
    , current = currTyp 
    , result = error "mkCtx: no Result"
    , variables = Map.empty -- attrMap c
    , pos = error "mkCtx: no position"
    }

varCtx :: TypingBodyExpr body expr (Map String Typ)
varCtx = fmap variables ask

typeOfVar :: String -> TypingBodyExpr body expr (Maybe Typ)
typeOfVar "Result" = (Just . result) `fmap` ask
typeOfVar str = Map.lookup (map toLower str) `fmap` varCtx 

typeOfVar' :: String -> TypingBodyExpr body expr Typ
typeOfVar' str 
    = do mV <- typeOfVar str
         m <- varCtx
         case mV of
           Just v -> return v
           Nothing -> 
               throwErrorPos (concat ["Variable not found: ", str, ".", show m])

addDeclsToMap :: [Decl] -> Map String Typ -> Map String Typ
addDeclsToMap = Map.union . declsToMap

addDecls :: [Decl] -> TypeContext body expr -> TypeContext body expr
addDecls ds ctx = ctx {variables = addDeclsToMap ds (variables ctx)}

setResult :: AbsRoutine body' expr -> 
             TypeContext body expr -> TypeContext body expr
setResult f tc = tc {result = featureResult f}
