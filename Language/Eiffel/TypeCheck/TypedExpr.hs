module Language.Eiffel.TypeCheck.TypedExpr where

import Language.Eiffel.Eiffel (Typ (..), BinOp, UnOp, ClassName)
import Language.Eiffel.Class
import Language.Eiffel.Clause
import Language.Eiffel.Feature
import qualified Language.Eiffel.Expr as E
import Language.Eiffel.Expr (Expr, UnPosExpr)
import Language.Eiffel.Stmt
import Language.Eiffel.Position

type TClass = ClasBody TExpr
type TRoutine = RoutineWithBody TExpr
type TStmt = PosAbsStmt TExpr
type UnPosTStmt = AbsStmt TExpr

type TExpr = Pos UnPosTExpr

data UnPosTExpr 
  = Call TExpr String [TExpr] Typ
  | Access TExpr String Typ
  | Var String Typ
  | BinOpExpr BinOp TExpr TExpr Typ
  | UnOpExpr UnOp TExpr Typ
  | Attached ClassName TExpr String
  | ResultVar Typ
  | CurrentVar Typ
  | Box Typ TExpr
  | Unbox Typ TExpr
  | Cast Typ TExpr
  | LitChar Char
  | LitString String
  | LitInt Int
  | LitBool Bool
  | LitVoid Typ
  | LitDouble Double deriving (Show, Eq)

untype :: TClass -> Clas
untype = classMapExprs untypeFeat untypeClause untypeConstant

untypeClause :: Clause TExpr -> Clause Expr
untypeClause (Clause label e) = Clause label (untypeExpr e)

untypeContract (Contract inherit clauses) = 
  Contract inherit (map untypeClause clauses)

untypeConstant (Constant froz decl expr) = 
  Constant froz decl (untypeExpr expr)

untypeFeat :: TRoutine -> Routine
untypeFeat tfeat = tfeat { routineImpl = untypeImpl (routineImpl tfeat)
                         , routineReq  = untypeContract (routineReq tfeat)
                         , routineEns  = untypeContract (routineEns tfeat)
                         }

untypeImpl :: RoutineBody TExpr -> RoutineBody Expr
untypeImpl body = body {routineBody = untypeStmt (routineBody body)}

untypeStmt :: TStmt -> Stmt
untypeStmt = fmap untypeStmt'

untypeStmt' :: UnPosTStmt -> UnPosStmt
untypeStmt' (Assign l e) = Assign (untypeExpr l) (untypeExpr e)
untypeStmt' (CallStmt e) = CallStmt (untypeExpr e)
untypeStmt' (Block ss)   = Block (map untypeStmt ss)
untypeStmt' BuiltIn      = BuiltIn
untypeStmt' (If e body elseIfs elsePart) = 
  let untypeElseIf (ElseIfPart cond s) = 
        ElseIfPart (untypeExpr cond) (untypeStmt s)
  in If (untypeExpr e) (untypeStmt body)
        (map untypeElseIf elseIfs) (fmap untypeStmt elsePart)
untypeStmt' (Create typeMb targ name es) = 
  Create typeMb (untypeExpr targ) name (map untypeExpr es)
untypeStmt' s = error (show s)



untypeExpr :: TExpr -> Expr
untypeExpr = fmap untypeExpr'

untypeExpr' :: UnPosTExpr -> UnPosExpr
untypeExpr' (Call trg name args _r)
    = E.QualCall (untypeExpr trg) name (map untypeExpr args)
untypeExpr' (Access trg name _r)
    = E.QualCall (untypeExpr trg) name []
untypeExpr' (Var s _t)
    = E.VarOrCall s
untypeExpr' (CurrentVar _t)
    = E.CurrentVar
untypeExpr' (Cast t e) 
    = E.Cast t (untypeExpr e)
untypeExpr' (ResultVar _t)
    = E.ResultVar
           --- | BinOpExpr BinOp TExpr TExpr Typ
           --- | UnOpExpr UnOp TExpr Typ
           --- | Attached ClassName TExpr String
           --- | Box Typ TExpr
           --- | Unbox Typ TExpr
           --- | LitChar Char
           --- | LitString String
           --- | LitInt Int
           --- | LitBool Bool
           --- | LitVoid Typ
           --- | LitDouble Double deriving (Show, Eq)
untypeExpr' s = error $ show s      

texpr :: TExpr -> Typ
texpr = texprTyp . contents

texprTyp :: UnPosTExpr -> Typ
texprTyp (LitInt _)  = IntType
texprTyp (LitBool _) = BoolType
texprTyp (LitDouble _) = DoubleType
texprTyp (LitVoid  t) = t
texprTyp (Var _ t)   = t
texprTyp (Cast t _)  = t
texprTyp (ResultVar t) = t
texprTyp (CurrentVar t) = t
texprTyp (Call _ _ _ t) = t
texprTyp (Access _ _ t) = t
texprTyp (BinOpExpr _ _ _ t) = t
texprTyp (UnOpExpr _ _ t) = t
texprTyp (Box _ te) = texpr te
texprTyp (Unbox t _) = t
texprTyp (LitChar _) = ClassType "CHARACTER" []
texprTyp (Attached _ _ _) = error "texprTyp: attachment test unimplemented"
texprTyp (LitString _) = ClassType "STRING" []