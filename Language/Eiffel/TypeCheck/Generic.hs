module Language.Eiffel.TypeCheck.Generic where

import Control.Applicative
import Control.Monad

import Data.Maybe

import Language.Eiffel.TypeCheck.Context
import qualified Language.Eiffel.TypeCheck.TypedExpr as T

import Language.Eiffel.Syntax
import Language.Eiffel.Util
import Language.Eiffel.Position

import Util.Monad

-- for checking declarations `a : ARRAY [INTEGER]'
checkTypeInst :: Typ -> TypingBody body ()
checkTypeInst t@(ClassType _ ts) = do
  clsGens  <- generics `fmap` lookupClass t
  satGensThrow clsGens ts
checkTypeInst _ = return ()

satGensThrow :: [Generic] -> [Typ] -> TypingBody body ()
satGensThrow gs ts = do
  guardThrow (length gs == length ts) "resolveGeneric: diff length"             
  zipWithM_ satGenThrow gs ts
  
satGenThrow :: Generic -> Typ -> TypingBody body ()
satGenThrow g t = do
  sat <- satisfiesGeneric g t
  guardThrow sat "satGenThrow: unsatisfied"

satisfiesGeneric :: Generic -> Typ -> TypingBody body Bool
satisfiesGeneric _g _t = return True

-- during lookup of the class as in `a.f'

resolveIFace :: Typ -> TypingBody body (AbsClas body Expr)
resolveIFace t@(ClassType _ ts) = updateGenerics ts `fmap` lookupClass t
resolveIFace (Like ident) = do
  T.CurrentVar t <- contents <$> currentM
  -- res <- lookupClass t --unlikeType t (Like ident)
  resolveIFace t
resolveIFace (Sep _ _ t)  = resolveIFace (ClassType t [])
resolveIFace t = error $ "resolveIFace: called on " ++ show t

type GenUpd a = Typ -> Typ -> a -> a

updateGenerics :: [Typ] -> AbsClas body Expr -> AbsClas body Expr
updateGenerics ts ci =
    let gs = map (\ gen -> ClassType (genericName gen) []) (generics ci)
        f  = foldl (.) id (zipWith updateGeneric gs ts)
        newClass = f ci
    in newClass -- { generics = [] }

updateGeneric :: GenUpd (AbsClas body Expr) 
updateGeneric g t = 
  classMapAttributes (updateAttribute g t) . 
  classMapRoutines (updateFeatDecl g t)

updateFeatDecl :: GenUpd (AbsRoutine body Expr)
updateFeatDecl g t fd = 
    fd 
    { routineArgs = map (updateDecl g t) (routineArgs fd)
    , routineResult = updateTyp g t (routineResult fd)
    }

updateAttribute g t a = a {attrDecl = updateDecl g t (attrDecl a)}

updateDecl :: GenUpd Decl
updateDecl g t (Decl n t') = Decl n (updateTyp g t t')

updateTyp :: GenUpd Typ
updateTyp g t t'@(ClassType name types)
  | g == t' = t
  | otherwise = ClassType name (map (updateTyp g t) types)
updateTyp g t t'@(TupleType typesOrDecls)
  | g == t' = t
  | otherwise = case typesOrDecls of
    Left types -> TupleType (Left $ map (updateTyp g t) types)
    Right decls -> TupleType (Right $ map (updateDecl g t) decls)
updateTyp g t t' 
  | g == t' = t
  | otherwise =  t'

unlike current clas (Decl n (Like ident)) = 
  Decl n <$> unlikeType current clas (Like ident)
unlike _ _ d =  return d

unlikeType current clas (Like "Current") = return current
unlikeType current clas (Like ident) = do
  typeMb <- typeOfVar ident
  pos <- currentPos
  case (featureResult <$> findFeatureEx clas ident) <|> typeMb of
    Nothing -> error $ "unlikeType: can't find " ++ ident ++ 
                       " in " ++ show current ++ "," ++ show pos
    Just resT -> unlikeType current clas resT
unlikeType current clas (ClassType name gs) = 
  ClassType name <$> mapM (unlikeType current clas) gs