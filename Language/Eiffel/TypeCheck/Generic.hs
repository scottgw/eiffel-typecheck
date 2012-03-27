module Language.Eiffel.TypeCheck.Generic 
       (resolveIFace, unlike, unlikeType, updateGeneric, updateGenerics) where

import Control.Applicative

import Language.Eiffel.TypeCheck.Context
import qualified Language.Eiffel.TypeCheck.TypedExpr as T

import Language.Eiffel.Syntax
import Language.Eiffel.Util
import Language.Eiffel.Position

import Util.Monad

resolveIFace :: Typ -> TypingBody body (AbsClas body Expr)
resolveIFace t@(ClassType _ ts) = updateGenerics ts `fmap` lookupClass t
resolveIFace (Like _) = do
  T.CurrentVar t <- contents <$> currentM
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

unlike curr clas (Decl n (Like ident)) = 
  Decl n <$> unlikeType curr clas (Like ident)
unlike _ _ d =  return d

unlikeType curr _ (Like "Current") = return curr
unlikeType curr clas (Like ident) = do
  typeMb <- typeOfVar ident
  p <- currentPos
  case (featureResult <$> findFeatureEx clas ident) <|> typeMb of
    Nothing -> error $ "unlikeType: can't find " ++ ident ++ 
                       " in " ++ show curr ++ "," ++ show p
    Just resT -> unlikeType curr clas resT
unlikeType curr clas (ClassType name gs) = 
  ClassType name <$> mapM (unlikeType curr clas) gs
unlikeType _ _ t = return t