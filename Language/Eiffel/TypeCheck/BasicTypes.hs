{-# LANGUAGE FlexibleContexts #-}

module Language.Eiffel.TypeCheck.BasicTypes 
       (guardTypeIs, numericCanBe, conformThrow) where

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

numericCanBe (T.LitInt 0) t =
  isIntegerType t || isNaturalType t || isRealType t
numericCanBe (T.LitDouble n) t = isRealType t
numericCanBe (T.LitInt i) t
  | isIntegerType t || isNaturalType t =
    let (lower, upper) = typeBounds t
    in lower <= fromIntegral i && fromIntegral i <= upper
  | otherwise = False
numericCanBe e t 
  | T.texprTyp e == (ClassType "INTEGER_32" []) &&
    (t == (ClassType "REAL_64" []) || t == (ClassType "REAL_32" [])) = True
  | T.texprTyp e == (ClassType "INTEGER_32" []) &&
    t == (ClassType "INTEGER_64" []) = True
  | isNaturalType (T.texprTyp e) && --  == ClassType "NATURAL_8" [] &&
    (t == ClassType "INTEGER_32" [] || t == ClassType "NATURAL_32" []) = True
  | isIntegerType (T.texprTyp e) &&
    (t == ClassType "INTEGER_32" [] || t == ClassType "NATURAL_32" []) = True
  | otherwise = False

guardTypePred :: (Typ -> Bool) -> String -> Typ -> TypingBody body Typ
guardTypePred p s t = guardThrow (p t) s >> return t

guardTypeIs typ expr = 
  let exprType = T.texpr expr
  in guardTypePred (== typ) 
                   ("require " ++ show typ ++ " actual " ++ show exprType)
                   (T.texpr expr)

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
  fromCls <- lookupClass fromType
  toCls <- lookupClass toType
  p <- currentPos
  let convTo (ConvertTo _ types) = toType `elem` types 
      convTo _ = False 
      convertersTo = find convTo (S.converts fromCls)
      
      convFrom (ConvertFrom _ types) = fromType `elem` types
      convFrom _ = False
      convertersFrom = find convFrom (S.converts toCls)
      
  case convertersTo <|> convertersFrom of
    Nothing -> return Nothing
    Just (ConvertTo name _) -> 
      return $ Just $ \t -> attachPos p $ T.Call t name [] toType
    Just (ConvertFrom name _) -> 
      return $ Just $ \t -> attachPos p $ T.CreateExpr fromType name [t]


conforms :: Typ -> Typ -> TypingBody body (Maybe (TExpr -> TExpr))
conforms VoidType t
    | isBasic t = return Nothing
    | otherwise = return (Just (inheritPos (T.Cast t)))
conforms (Sep _ _ t1) (Sep _ _ t2) = 
    conforms (ClassType t1 []) (ClassType t2 [])
conforms (TupleType typesDecls1) tup@(TupleType typeDecls2)
    | either null null typesDecls1 = return (Just $ inheritPos (T.Cast tup))
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
