module Language.Eiffel.TypeCheck.Class (clas, clasM, clasT) where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.Reader

import Language.Eiffel.Eiffel

import qualified Language.Eiffel.TypeCheck.TypedExpr as T
import Language.Eiffel.TypeCheck.TypedExpr (TStmt, TFeature, TClass)

import Language.Eiffel.TypeCheck.BasicTypes
import Language.Eiffel.TypeCheck.Context
import Language.Eiffel.TypeCheck.Expr

featureEnv :: Feature -> TypeContext -> TypeContext
featureEnv f = 
    addDecls (featureArgs f ++ featureLocal (featureImpl f)) . setResult f
  
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

featClause :: FeatureClause FeatureBody Expr 
              -> Typing (FeatureClause FeatureBody T.TExpr)
featClause fClause = do
  fs <- mapM feature (features fClause)
  cs <- mapM constt (constants fClause)
  as <- mapM attr (attributes fClause)
  return (fClause { features = fs
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

feature :: Feature -> Typing TFeature
feature f = 
    local (featureEnv f) 
              (do
                pre  <- contract (featureReq f)
                post <- contract (featureEns f)
                body <- feature' f
                return $ updFeat f pre body post
              )

updFeat :: FeatureWithBody exp -> Contract exp'
        -> PosAbsStmt exp' -> Contract exp' -> FeatureWithBody exp'
updFeat f pre body post = 
    f { featureImpl = updFeatBody (featureImpl f) body
      , featureReq = pre
      , featureEns = post}

feature' :: Feature -> Typing TStmt
feature' = stmt . featureBody . featureImpl

stmt :: Stmt -> Typing TStmt
stmt s = setPosition (position s) (uStmt (contents s))

uStmt :: UnPosStmt -> Typing TStmt

uStmt (CallStmt e) = do
  e' <- typeOfExpr e
  tagPos (CallStmt e')
  
uStmt (Assign s e) = do
  s' <- typeOfExpr s
  e' <- flip conformThrow (T.texpr s') =<< typeOfExpr e
  return $ inheritPos (Assign s') e'
--  t  <- conformThrow e' tVar
--  case contents e' of
--    T.LitVoid _ -> tagPos (T.LitVoid t) >>= tagPos . Assign s
--    _ -> tagPos (Assign s e')

uStmt (If cond body elseIfs elsePart) = do
  cond' <- typeOfExpr cond
  guardThrow (isBool $ T.texpr cond') "Stmt: If requires Bool"
  body' <- stmt body
  let checkElseIf (ElseIfPart c s) = do
        c' <- typeOfExpr c
        guardThrow (isBool $ T.texpr c') "Stmt: ElseIf requires Bool"
        s' <- stmt s
        return (ElseIfPart c' s')
  elseIfs' <- mapM checkElseIf elseIfs
  else' <- case elsePart of
              Nothing -> return Nothing
              Just e  -> Just `fmap` stmt e
  tagPos (If cond' body' elseIfs' else')

uStmt (Loop setup invs cond body) = do
  setup' <- stmt setup
  invs' <- mapM clause invs
  cond' <- typeOfExpr cond
  case T.texpr cond' of
    BoolType -> return ()
    _        -> throwError "loop condition should be of type boolean"
  body' <- stmt body
  tagPos (Loop setup' invs' cond' body')

uStmt (Block ss) = Block `fmap` mapM stmt ss >>= tagPos

uStmt (Print e)  = do
  e' <- typeOfExpr e
  guardThrow (isInt $ T.texpr e') "uStmt: Print not int"
  tagPos (Print e')

uStmt (PrintD e)  = do
  e' <- typeOfExpr e
  guardThrow (isDouble $ T.texpr e') "uStmt: Print not double"
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