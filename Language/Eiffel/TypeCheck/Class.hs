module Language.Eiffel.TypeCheck.Class 
       (clas, clasM, typeInterfaces, typedPre, runTyping) where

import Control.Applicative
import Control.Monad.Reader

import Data.Maybe

import Debug.Trace

import Language.Eiffel.Syntax
import Language.Eiffel.Position
import Language.Eiffel.Util

import qualified Language.Eiffel.TypeCheck.TypedExpr as T
import Language.Eiffel.TypeCheck.TypedExpr (TStmt, TClass)
import Language.Eiffel.TypeCheck.Context
import Language.Eiffel.TypeCheck.Generic
import Language.Eiffel.TypeCheck.Expr

import Util.Monad

traceShow' x = traceShow x x

-- unlikeInterfaceM inters clas = runTyping inters clas (unlikeInterface clas)

-- unlikeDecls clsType decls = 
--   local (addDecls noLikes) (mapM (unlike clsType) decls)
--     where isLike (Like _) = True
--           isLike _        = False
--           (likes, noLikes) = span (isLike . declType) decls

-- findInParents :: Typ -> String -> TypingBody ctxBody (Maybe FeatureEx)
-- findInParents typ name = do
--   cls <- lookupClass typ
--   case findFeatureEx cls name of
--     Just r -> return (Just r)
--     Nothing -> do
--       let notUndefined ih = 
--             name `notElem` concatMap undefine (inheritClauses ih)
--           validParents = filter notUndefined (inherit cls)
--           parentTypes = 
--             concatMap (map inheritClass . inheritClauses) validParents
--       res <- mapM (`findInParents` name) parentTypes
--       return (msum res)
  

-- unlike :: Typ -> Decl -> TypingBody ctxBody Decl
-- unlike current (Decl n (Like "Current")) = return (Decl n current)
-- unlike current (Decl n (Like ident)) = do
--   typeMb <- typeOfVar ident
--   case typeMb of
--     Just t -> return (Decl n t)
--     Nothing -> do 
--       featMb <- findInParents current ident
--       cls <- lookupClass current
--       let feat = fromMaybe (error $ "unlike: " ++ n ++ ": like " ++ ident ++ 
--                                     " in " ++ show current)
--                            featMb
--       Decl _ resTyp <- unlike current (Decl "__unlike" $ featureResult feat)
--       return (Decl n resTyp)
-- unlike _ d =  return d

routineStmt :: RoutineBody Expr -> TypingBody body TStmt
routineStmt = stmt . routineBody


routineEnv :: AbsRoutine body Expr
              -> TypingBody ctxBody a
              -> TypingBody ctxBody a
routineEnv f m = do
  curr <- current <$> ask
  clas <- flatten curr
  dcls <- unlikeDecls curr clas (routineArgs f)
  local (addDecls dcls . setResult f) m
 
runTyping :: [AbsClas ctxBody Expr]
             -> AbsClas body expr
             -> TypingBody ctxBody a
             -> Either String a
runTyping cs curr m = idErrorRead m (mkCtx (cType curr) cs)

clasM :: [AbsClas ctxBody Expr] 
         -> AbsClas (RoutineBody Expr) Expr 
         -> Either String TClass
clasM cs c = runTyping cs c (clas c routineWithBody)

clas :: AbsClas t Expr 
        -> (t -> TypingBody ctxBody body) 
        -> TypingBody ctxBody (AbsClas body T.TExpr)
clas c rtnBodyCheck = do
    fcs  <- mapM (featClause rtnBodyCheck) (featureClauses c)
    invs <- mapM clause (invnts c)
    return $ c {featureClauses = fcs, invnts = invs}


typeInterfaces :: [ClasInterface] -> 
                  IO (Either String [AbsClas EmptyBody T.TExpr])
typeInterfaces inters = 
  let 
    go :: ClasInterface -> IO (AbsClas EmptyBody T.TExpr)
    go i = do print (className i)
              case runTyping inters i (interface i) of
                Left s -> error s
                Right i -> return i
  in do inters' <- mapM go inters
        return (Right inters')
     

interface :: AbsClas EmptyBody Expr 
             -> TypingBody ctxBoxy (AbsClas EmptyBody T.TExpr)
interface curr = clas curr return

cType :: AbsClas body exp -> Typ
cType c =
  ClassType (className c) 
            (map (\ g -> ClassType (genericName g) []) (generics c))

typedPre :: [ClasInterface] -> ClasInterface 
            -> String -> Either String (Contract T.TExpr)
typedPre cis classInt name = idErrorRead go (mkCtx (cType classInt) cis)
  where Just rout = findFeature classInt name 
        go = routineEnv rout
                   (do r <- routine (const (return EmptyBody)) rout
                       return (routineReq r))

featClause :: (body -> TypingBody ctxBody body')  
              -> FeatureClause body Expr 
              -> TypingBody ctxBody (FeatureClause body' T.TExpr)
featClause  checkBody fClause = do
  fs <- mapM (routine checkBody) (routines fClause)
  cs <- mapM constt (constants fClause)
  as <- mapM attr (attributes fClause)
  return (fClause { routines = fs
                  , constants = cs
                  , attributes = as
                  })

attr :: Attribute Expr -> TypingBody body (Attribute T.TExpr)
attr a = do
  reqs <- contract (attrReq a)
  enss <- contract (attrEns a)
  return (a { attrReq = reqs
            , attrEns = enss
            })

contract :: Contract Expr -> TypingBody body (Contract T.TExpr)
contract (Contract inher cs) = Contract inher `fmap` mapM clause cs

constt :: Constant Expr -> TypingBody body (Constant T.TExpr)
constt (Constant froz d e) = Constant froz d `fmap` typeOfExpr e
-- TODO: Match the type of the expression with the 
-- delcared type of the constant.

routine :: (body -> TypingBody ctxBody body')
           -> AbsRoutine body Expr 
           -> TypingBody ctxBody (AbsRoutine body' T.TExpr)
routine checkBody f = 
    routineEnv f
      (do
          pre  <- contract (routineReq f)
          post <- contract (routineEns f)
          body <- checkBody (routineImpl f)
          resc <- rescue (routineRescue f)
          return $ f { routineReq = pre
                     , routineImpl = body
                     , routineEns = post
                     , routineRescue = resc
                     }
          )

rescue :: Maybe [Stmt] -> TypingBody ctxBody (Maybe [TStmt])
rescue Nothing = return Nothing
rescue (Just ss) = Just <$> mapM stmt ss

routineWithBody :: RoutineBody Expr -> TypingBody body (RoutineBody T.TExpr)
routineWithBody body = do
  stmt <- routineStmt body
  return (body {routineBody = stmt})

stmt :: Stmt -> TypingBody body TStmt
stmt s = setPosition (position s) (uStmt (contents s))

uStmt :: UnPosStmt -> TypingBody body TStmt

uStmt (CallStmt e) = do
  e' <- typeOfExpr e
  tagPos (CallStmt e')
  
uStmt (Assign s e) = do
  s' <- typeOfExpr s
  e' <- typeOfExprIs (T.texpr s') e
  return $ inheritPos (Assign s') e'

uStmt (If cond body elseIfs elsePart) = do
  cond' <- typeOfExprIs boolType cond
  body' <- stmt body
  let checkElseIf (ElseIfPart c s) = do
        c' <- typeOfExprIs boolType c
        s' <- stmt s
        return (ElseIfPart c' s')
  elseIfs' <- mapM checkElseIf elseIfs
  else' <- case elsePart of
              Nothing -> return Nothing
              Just e  -> Just `fmap` stmt e
  tagPos (If cond' body' elseIfs' else')

uStmt (Loop setup invs cond body var) = do
  setup' <- stmt setup
  invs' <- mapM clause invs
  cond' <- typeOfExprIs boolType cond
  body' <- stmt body
  var' <- maybe (return Nothing) (fmap Just . typeOfExprIs intType) var
  tagPos (Loop setup' invs' cond' body' var')

uStmt (Block ss) = Block `fmap` mapM stmt ss >>= tagPos

uStmt (Print e)  = do
  e' <- typeOfExprIs intType e
  tagPos (Print e')

uStmt (PrintD e)  = do
  e' <- typeOfExprIs realType e
  tagPos (PrintD e')

uStmt (Create typeMb vr fName args) = do
  call <- tagPos (QualCall vr fName args) >>= typeOfExpr
  let call' = case contents call of
                T.Cast _ c -> c
                T.Call {} -> call
                _ -> error "uStmt: create only on casts or calls"
  let T.Call trg _ tArgs res = contents call'
  let ClassType _ _ = T.texpr trg
  guardThrow (res == NoType) 
                 "There must be no return type for create"
  guardThrow (maybe True (T.texpr trg ==) typeMb) -- FIXME: This should be inherits
                 "Target type doesn't match dynamic type"
  tagPos (Create typeMb trg fName tArgs)

uStmt BuiltIn = tagPos BuiltIn

-- uStmt s = error $ "uStmt: not implemented " ++ show s