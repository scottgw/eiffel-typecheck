{-# LANGUAGE FlexibleContexts #-}

module Language.Eiffel.TypeCheck.BasicTypes where

import Control.Applicative
import Control.Monad
import Control.Monad.Error

import Data.List (find)

import Language.Eiffel.Syntax as S
import Language.Eiffel.Position
import Language.Eiffel.Util

import qualified Language.Eiffel.TypeCheck.TypedExpr as T
import Language.Eiffel.TypeCheck.TypedExpr (TExpr)
import Language.Eiffel.TypeCheck.Context
import Language.Eiffel.TypeCheck.Generic

import Util.Monad

isInt, isDouble, isBool :: Typ -> Bool
isInt (ClassType name []) = True
isInt _       = False

isDouble (ClassType name []) = True
isDouble _          = False

isNum :: Typ -> Bool
isNum t = isDouble t || isInt t

isBool = (== boolType)

guardTypePred :: (Typ -> Bool) -> String -> Typ -> TypingBody body Typ
guardTypePred p s t = guardThrow (p t) s >> return t

guardTypeIs typ expr = 
  guardTypePred (== typ)
                ("require " ++ show typ)
                (T.texpr expr)

-- inClass :: ClassFeature a body Expr => String -> Typ -> TypingBody body a
inClass = inClass' resolveIFace

-- inGenClass  :: ClassFeature a body Expr => 
--                String -> Typ -> TypingBody body a
inGenClass   = inClass' lookupClass

inClass' :: -- ClassFeature a body expr =>
            (Typ -> TypingBody body (AbsClas body expr))
            -> String
            -> Typ
            -> TypingBody body FeatureEx
inClass' lookupC fName t = do
  ci   <- lookupC t
  maybeThrow (findFeature ci fName) $ "No Feature Found: " ++ fName ++ " in " ++ show t ++ " with " ++ show (map (featureName :: FeatureEx -> String) (allFeatures ci))


conformThrow :: TExpr -> Typ -> TypingBody body TExpr
conformThrow expr t = do
  r <- conforms (T.texpr expr) t
  case r of
    Just f  -> return (f expr)
    Nothing -> do
      conv <- convertsTo (T.texpr expr) t
      case conv of
        Nothing -> 
          throwError (show expr ++ " doesn't conform or convert to " ++ show t)
        Just f -> return (f expr)

convertsTo :: Typ -> Typ -> TypingBody ctxBody (Maybe (TExpr -> TExpr))
convertsTo fromType toType = do
  cls <- lookupClass fromType
  p <- currentPos
  let convTo (ConvertTo name types) = toType `elem` types 
      convTo _ = False 
      converters = find convTo (S.converts cls)
  case converters of
    Nothing -> return Nothing
    Just (ConvertTo name _) -> 
      return $ Just $ \t -> attachPos p $ T.Call t name [] toType
        

conforms :: Typ -> Typ -> TypingBody body (Maybe (TExpr -> TExpr))
conforms VoidType t
    | isBasic t = return Nothing
    | otherwise = return (Just (inheritPos (T.Cast t)))
conforms (Sep _ _ t1) (Sep _ _ t2) = 
    conforms (ClassType t1 []) (ClassType t2 [])
conforms _t VoidType = return Nothing
conforms _ t | t == anyType = return $ Just $ inheritPos (T.Cast anyType)
conforms t1 t2
    | isBasic t1 && isBasic t2 && t1 == t2 = return (Just id)
    | t1 == t2 = return (Just id)
    | otherwise = 
        let
            ihts :: TypingBody body [Typ]
            ihts = allInheritedTypes <$> resolveIFace t1

            conformss :: [Typ] -> TypingBody body [Maybe (TExpr -> TExpr)]
            conformss = mapM (flip conforms t2)

            cast :: TypingBody body (Maybe (TExpr -> TExpr)) 
            cast = fmap msum . conformss =<< ihts

            castWithPos :: TExpr -> TExpr
            castWithPos = inheritPos (T.Cast t2)

            maybeCast :: Maybe (TExpr -> TExpr) -> Maybe (TExpr -> TExpr)
            maybeCast = fmap (castWithPos .)
        in
             fmap maybeCast cast
