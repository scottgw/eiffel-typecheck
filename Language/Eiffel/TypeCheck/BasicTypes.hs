{-# LANGUAGE FlexibleContexts #-}

module Language.Eiffel.TypeCheck.BasicTypes where

import Control.Applicative
import Control.Monad
import Control.Monad.Error

import Language.Eiffel.Syntax
import Language.Eiffel.Position
import Language.Eiffel.Util

import qualified Language.Eiffel.TypeCheck.TypedExpr as T
import Language.Eiffel.TypeCheck.TypedExpr (TExpr)
import Language.Eiffel.TypeCheck.Context
import Language.Eiffel.TypeCheck.Generic

import Util.Monad

isInt, isDouble, isBool :: Typ -> Bool
isInt IntType = True
isInt _       = False

isDouble DoubleType = True
isDouble _          = False

isOtherNumType (ClassType name _) =
  name `elem` ["INTEGER_32"]

isNum :: Typ -> Bool
isNum t = isDouble t || isInt t || isOtherNumType t

isBool BoolType = True
isBool _        = False

unOpTypes :: UnOp -> Typ -> TypingBody body Typ
unOpTypes Old = return
unOpTypes Not = guardTypePred isBool "Not requires boolean"
unOpTypes Neg = guardTypePred isNum "Negation requires number"
unOpTypes Sqrt = guardTypePred isDouble "Sqrt requires double"

guardTypePred :: (Typ -> Bool) -> String -> Typ -> TypingBody body Typ
guardTypePred p s t = guardThrow (p t) s >> return t

guardTypeIs typ expr = 
  guardTypePred (== typ)
                ("require " ++ show typ)
                (T.texpr expr)

type BinOpTyping body = Typ -> Typ -> TypingBody body (Typ, Typ)

opTypes :: BinOp -> BinOpTyping body
opTypes Add = numTyper Add
opTypes Sub = numTyper Sub
opTypes Mul = numTyper Mul
opTypes Div = numTyper Div
opTypes Or  = biTyper Or  isBool isBool BoolType
opTypes OrElse  = biTyper OrElse  isBool isBool BoolType
opTypes And = biTyper And isBool isBool BoolType
opTypes AndThen = biTyper AndThen isBool isBool BoolType
opTypes Implies = biTyper Implies isBool isBool BoolType
opTypes r@(RelOp _ _) = relOpTyper r
opTypes (SymbolOp _) = error "opTypes: arbitrary symbol operators not yet supported"
opTypes o = error $ "opTypes: unknown symbol " ++ show o

castTyp :: Typ -> TExpr -> TExpr
castTyp DoubleType te = case T.texprTyp (contents te) of
                          DoubleType -> te
                          _          -> attachPos (position te) 
                                        (T.Cast DoubleType te)
castTyp IntType    te = case T.texprTyp (contents te) of
                          IntType -> te
                          _       -> attachPos (position te) (T.Cast IntType te)
castTyp _          te = case T.texprTyp (contents te) of
                          IntType    -> attachPos (position te) 
                                        (T.Cast IntType te)
                          DoubleType -> attachPos (position te) 
                                        (T.Cast DoubleType te)
                          _          -> te

castOp :: BinOp -> Typ -> BinOp
castOp (RelOp r _) = RelOp r
castOp o = const o

liftNum :: Typ -> Typ -> Typ
liftNum DoubleType DoubleType = DoubleType
liftNum DoubleType IntType    = DoubleType
liftNum IntType DoubleType    = DoubleType
liftNum IntType IntType       = IntType
liftNum BoolType BoolType     = BoolType
liftNum t1 t2 | t1 == t2      = t1
              | otherwise     = error $ "liftnum: " ++ show (t1,t2)

relOpTyper :: BinOp -> BinOpTyping body
relOpTyper = eqTyper

eqTyper :: BinOp -> BinOpTyping body
eqTyper op t1 t2 = do
  guardThrow (t1 == t2) $ "Types not the same for " ++ show op
  return (BoolType, liftNum t1 t2)

numTyper :: BinOp -> BinOpTyping body
numTyper op t1 t2 = biTyper op isNum isNum (liftNum t1 t2) t1 t2

biTyper :: BinOp -> (Typ -> Bool) -> (Typ -> Bool) -> Typ -> 
           BinOpTyping body
biTyper op lf rf resTyp t1 t2 = do
  guardThrow (lf t1) $ "First type is wrong " ++ show op ++ " got " ++ show t1
  guardThrow (rf t2) $ "Second type is wrong " ++ show op ++ " got " ++ show t2
  return (resTyp, liftNum t1 t2)

inClass :: ClassFeature a body Expr => String -> Typ -> TypingBody body a
inClass = inClass' resolveIFace

inGenClass  :: ClassFeature a body Expr => 
               String -> Typ -> TypingBody body a
inGenClass   = inClass' lookupClass

inClass' :: ClassFeature a body expr =>
            (Typ -> TypingBody body (AbsClas body expr))
            -> String
            -> Typ
            -> TypingBody body a
inClass' lookupC fName t = do
  ci   <- lookupC t
  maybeThrow (findFeature ci fName) $ "No Feature Found: " ++ fName


conformThrow :: TExpr -> Typ -> TypingBody body TExpr
conformThrow expr t = do
  r <- conforms (T.texpr expr) t
  case r of
    Just f  -> return (f expr)
    Nothing -> throwError (show expr ++ " doesn't conform to " ++ show t)
    


conforms :: Typ -> Typ -> TypingBody body (Maybe (TExpr -> TExpr))
conforms VoidType t
    | isBasic t = return Nothing
    | otherwise = return (Just (inheritPos (T.Cast t)))
conforms (Sep _ _ t1) (Sep _ _ t2) = 
    conforms (ClassType t1 []) (ClassType t2 [])
conforms _t VoidType = return Nothing
conforms _ (ClassType "ANY" []) = return $ Just $ inheritPos (T.Cast (ClassType "ANY" []))
conforms IntType (ClassType "INTEGER_32" []) = 
  return Nothing -- $ Just $ inheritPos (T.Cast IntType)
conforms (ClassType "INTEGER_32" []) IntType = 
  return $ Just $ inheritPos (T.Cast IntType)
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