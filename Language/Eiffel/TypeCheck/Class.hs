module Language.Eiffel.TypeCheck.Class (clas, clasM, clasT) where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.Reader

import Language.Eiffel.Eiffel

import qualified Language.Eiffel.TypeCheck.TypedExpr as T
import Language.Eiffel.TypeCheck.TypedExpr (TStmt, TRoutine, TClass)

import Language.Eiffel.TypeCheck.BasicTypes
import Language.Eiffel.TypeCheck.Context
import Language.Eiffel.TypeCheck.Expr

routineEnv :: Routine -> TypeContext -> TypeContext
routineEnv f = 
    addDecls (routineArgs f ++ routineDecls f) . setResult f

clasM :: [ClasInterface] -> Clas -> Either String TClass
clasM cs c = clasT cs c return

clasT :: [ClasInterface] -> Clas -> (TClass -> Typing b) 
         ->  Either String b
clasT cs c m = idErrorRead (clas c >>= m) (mkCtx c cs)

clas :: Clas -> Typing TClass
clas c = do
    fcs  <- mapM featClause (featureClauses c)
    invs <- mapM clause (invnts c)
    return $ c {featureClauses = fcs, invnts = invs}

featClause :: FeatureClause RoutineBody Expr 
              -> Typing (FeatureClause RoutineBody T.TExpr)
featClause fClause = do
  fs <- mapM routine (routines fClause)
  cs <- mapM constt (constants fClause)
  as <- mapM attr (attributes fClause)
  return (fClause { routines = fs
                  , constants = cs
                  , attributes = as
                  })

attr :: Attribute Expr -> Typing (Attribute T.TExpr)
attr a = do
  reqs <- contract (attrReq a)
  enss <- contract (attrEns a)
  return (a { attrReq = reqs
            , attrEns = enss
            })
    
contract :: Contract Expr -> Typing (Contract T.TExpr)
contract (Contract inherit cs) = Contract inherit `fmap` mapM clause cs

constt :: Constant Expr -> Typing (Constant T.TExpr)
constt (Constant froz d e) = Constant froz d `fmap` typeOfExpr e
-- TODO: Match the type of the expression with the 
-- delcared type of the constant.

routine :: Routine -> Typing TRoutine
routine f = 
    local (routineEnv f) 
              (do
                pre  <- contract (routineReq f)
                post <- contract (routineEns f)
                body <- routine' f
                return $ updFeat f pre body post
              )

updFeat :: RoutineWithBody exp -> Contract exp'
        -> PosAbsStmt exp' -> Contract exp' -> RoutineWithBody exp'
updFeat f pre body post = 
    f { routineImpl = updFeatBody (routineImpl f) body
      , routineReq = pre
      , routineEns = post}

routine' :: Routine -> Typing TStmt
routine' = stmt . routineBody . routineImpl

stmt :: Stmt -> Typing TStmt
stmt s = setPosition (position s) (uStmt (contents s))

uStmt :: UnPosStmt -> Typing TStmt

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

uStmt (DefCreate typeMb v) = 
  let VarOrCall _ = contents v 
  in uStmt (Create typeMb v "default_create" [])

uStmt BuiltIn = tagPos BuiltIn

-- uStmt s = error $ "uStmt: not implemented " ++ show s