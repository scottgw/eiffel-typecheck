module Language.Eiffel.TypeCheck.BasicTypes where

import Control.Applicative
import Control.Monad
import Control.Monad.Error

import Language.Eiffel.Eiffel

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

isNum :: Typ -> Bool
isNum t = isDouble t || isInt t

isBool BoolType = True
isBool _        = False

unOpTypes :: UnOp -> Typ -> Typing Typ
unOpTypes Not = guardTypePred isBool "Not requires boolean"
unOpTypes Neg = guardTypePred isNum "Negation requires number"
unOpTypes Sqrt = guardTypePred isDouble "Sqrt requires double"

guardTypePred :: (Typ -> Bool) -> String -> Typ -> Typing Typ
guardTypePred p s t = guardThrow (p t) s >> return t

guardTypeIs typ expr = 
  guardTypePred (== typ)
                ("require " ++ show typ)
                (T.texpr expr)

type BinOpTyping = Typ -> Typ -> Typing (Typ, Typ)

opTypes :: BinOp -> BinOpTyping
opTypes Add = numTyper Add
opTypes Sub = numTyper Sub
opTypes Mul = numTyper Mul
opTypes Div = numTyper Div
opTypes Or  = biTyper Or  isBool isBool BoolType
opTypes And = biTyper And isBool isBool BoolType
opTypes Implies = biTyper Implies isBool isBool BoolType
opTypes r@(RelOp _ _) = relOpTyper r
opTypes (SymbolOp _) = error "opTypes: arbitrary symbol operators not yet supported"

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

relOpTyper :: BinOp -> BinOpTyping
relOpTyper = eqTyper

eqTyper :: BinOp -> BinOpTyping
eqTyper op t1 t2 = do
  guardThrow (t1 == t2) $ "Types not the same for " ++ show op
  return (BoolType, liftNum t1 t2)

numTyper :: BinOp -> BinOpTyping
numTyper op t1 t2 = biTyper op isNum isNum (liftNum t1 t2) t1 t2

biTyper :: BinOp -> (Typ -> Bool) -> (Typ -> Bool) -> Typ -> 
           BinOpTyping
biTyper op lf rf resTyp t1 t2 = do
  guardThrow (lf t1) $ "First type is wrong " ++ show op ++ " got " ++ show t1
  guardThrow (rf t2) $ "Second type is wrong " ++ show op ++ " got " ++ show t2
  return (resTyp, liftNum t1 t2)

inClassGen, inClass :: String -> Typ -> Typing FeatureI
inClassGen = inClass' resolveIFace
inClass    = inClass' lookupClass

attrInClassGen, attrInClass :: String -> Typ -> Typing Decl
attrInClassGen = attrInClass' resolveIFace
attrInClass    = attrInClass' lookupClass

attrInClass' :: (Typ -> Typing ClasInterface) -> String -> Typ -> Typing Decl
attrInClass' lookupC fName t = do
  ci   <- lookupC t
  maybeThrow (findAttrInt ci fName) $ "No Attribute Found: " ++ fName

inClass' :: (Typ -> Typing ClasInterface) -> String -> Typ -> Typing FeatureI
inClass' lookupC fName t = do
  ci   <- lookupC t
  maybeThrow (findFeatureInt ci fName) $ "No Feature Found: " ++ fName

conformThrow :: TExpr -> Typ -> Typing TExpr
conformThrow expr t = do
  r <- conforms (T.texpr expr) t
  case r of
    Just f  -> return (f expr)
    Nothing -> throwError (show expr ++ " doesn't conform to " ++ show t)

conforms :: Typ -> Typ -> Typing (Maybe (TExpr -> TExpr))
conforms VoidType t 
    | isBasic t = return Nothing
    | otherwise = return (Just (inheritPos (T.Cast t)))
conforms (Sep _ _ t1) (Sep _ _ t2) = 
    conforms (ClassType t1 []) (ClassType t2 [])
conforms _t VoidType = return Nothing
conforms t1 t2
    | isBasic t1 && isBasic t2 && t1 == t2 = return (Just id)
    | t1 == t2 = return (Just id)
    | otherwise = 
        let
            ihts :: Typing [Typ]
            ihts = (map inheritClass . inherit) <$> resolveIFace t1

            conformss :: [Typ] -> Typing [Maybe (TExpr -> TExpr)]
            conformss = mapM (flip conforms t2)

            cast :: Typing (Maybe (TExpr -> TExpr)) 
            cast = fmap msum . conformss =<< ihts

            castWithPos :: TExpr -> TExpr
            castWithPos = inheritPos (T.Cast t2)

            maybeCast :: Maybe (TExpr -> TExpr) -> Maybe (TExpr -> TExpr)
            maybeCast = fmap (castWithPos .)
        in
             fmap maybeCast cast