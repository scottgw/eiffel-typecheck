module Language.Eiffel.TypeCheck.Generic where

import Control.Applicative
import Control.Monad

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
  cls <- lookupClass t
  let Just feat = findFeatureEx cls ident
      res = if ident == "Current"
            then t 
            else featureResult feat
  resolveIFace res
resolveIFace (Sep _ _ t)  = resolveIFace (ClassType t [])
resolveIFace t = error $ "resolveIFace: called on " ++ show t

type GenUpd a = ClassName -> Typ -> a -> a

updateGenerics :: [Typ] -> AbsClas body Expr -> AbsClas body Expr
updateGenerics ts ci =
    let gs = map genericName (generics ci)
        f  = foldl (.) id (zipWith updateGeneric gs ts)
    in f ci

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
updateTyp g t t'@(ClassType c' _)
    | g == c'   = t --ClassType  (map (updateTyp g t) gs)
    | otherwise = t'
updateTyp _ _ t' = t'