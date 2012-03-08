module Language.Eiffel.TypeCheck.Class (clas, clasM, clasT, typedPre) where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.Reader

import Language.Eiffel.Eiffel

import qualified Language.Eiffel.TypeCheck.TypedExpr as T
import Language.Eiffel.TypeCheck.TypedExpr (TStmt, TRoutine, TClass)

import Language.Eiffel.TypeCheck.BasicTypes
import Language.Eiffel.TypeCheck.Context
import Language.Eiffel.TypeCheck.Expr

routineEnv :: AbsRoutine body' Expr -> TypeContext body -> TypeContext body
routineEnv f = 
    addDecls (routineArgs f) . setResult f

clasM :: [AbsClas body Expr] -> Clas -> Either String TClass
clasM cs c = clasT cs c return

clasT :: [AbsClas body Expr] -> Clas -> (TClass -> TypingBody body a) 
         ->  Either String a
clasT cs c m = idErrorRead (clas c >>= m) (mkCtx (cType c) cs)

clas :: Clas -> TypingBody body TClass
clas c = do
    fcs  <- mapM (featClause routineWithBody) (featureClauses c)
    invs <- mapM clause (invnts c)
    return $ c {featureClauses = fcs, invnts = invs}

cType c =   
  ClassType (className c) 
            (map (\ g -> ClassType (genericName g) []) (generics c))

typedPre :: [ClasInterface] -> ClasInterface 
            -> String -> Either String (Contract T.TExpr)
typedPre cis classInt name = idErrorRead go (mkCtx (cType classInt) cis)
  where Just rout = findFeature classInt name 
        go = local (routineEnv rout)
                   (do r <- routine (const (return EmptyBody)) rout
                       return (routineReq r))


featClause :: (body Expr -> TypingBody body' (body T.TExpr))  
              -> FeatureClause body Expr 
              -> TypingBody body' (FeatureClause body T.TExpr)
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
contract (Contract inherit cs) = Contract inherit `fmap` mapM clause cs

constt :: Constant Expr -> TypingBody body (Constant T.TExpr)
constt (Constant froz d e) = Constant froz d `fmap` typeOfExpr e
-- TODO: Match the type of the expression with the 
-- delcared type of the constant.

routine :: (body Expr -> TypingBody body' (body T.TExpr))
           -> AbsRoutine body Expr 
           -> TypingBody body' (AbsRoutine body T.TExpr)
routine checkBody f = 
    local (routineEnv f) 
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

rescue Nothing = return Nothing
rescue (Just ss) = Just <$> mapM stmt ss

routineWithBody :: RoutineBody Expr -> TypingBody body (RoutineBody T.TExpr)
routineWithBody body = 
  local (addDecls (routineLocal body))
        (do stmt <- routineStmt body
            return (body {routineBody = stmt}))

routineStmt :: RoutineBody Expr -> TypingBody body TStmt
routineStmt = stmt . routineBody

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
  cond' <- typeOfExprIs BoolType cond
  body' <- stmt body
  let checkElseIf (ElseIfPart c s) = do
        c' <- typeOfExprIs BoolType c
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
  cond' <- typeOfExprIs BoolType cond
  body' <- stmt body
  var' <- maybe (return Nothing) (fmap Just . typeOfExprIs IntType) var
  tagPos (Loop setup' invs' cond' body' var')

uStmt (Block ss) = Block `fmap` mapM stmt ss >>= tagPos

uStmt (Print e)  = do
  e' <- typeOfExprIs IntType e
  tagPos (Print e')

uStmt (PrintD e)  = do
  e' <- typeOfExprIs DoubleType e
  tagPos (PrintD e')

uStmt (Create typeMb vr fName args) = do
  call <- tagPos (QualCall vr fName args) >>= typeOfExpr
  let call' = case contents call of
                T.Cast _ c -> c
                T.Call _ _ _ _ -> call
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