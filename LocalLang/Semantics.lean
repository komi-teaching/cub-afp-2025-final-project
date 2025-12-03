import LocalLang.AST
import LocalLang.Evaluator
import LocalLang.Ctx
import Mathlib.Logic.Relation

-- for rewriting (.funCall f es) in terms of let
def Expr.addBindings (ps : List String) (es : List Expr) (e : Expr)
  (_ : ps.length = es.length) : Expr :=
  (ps.zip es).foldl (fun e' (x, xe) => .letIn x xe e') e

inductive HeadSmallStep : Env → Expr → Expr → Prop where
  | const_step : HeadSmallStep V (.const n) (.value (.nat n))
  | var_step : V[x]? = some v →
      HeadSmallStep V (.var x) (.value v)
  | bin_op_step {op : BinOp}
      : n = op.eval n₁ n₂
      → HeadSmallStep V (.binOp op (.value (.nat n₁)) (.value (.nat n₂)))
        (.value (.nat (op.eval n₁ n₂)))
  | let_in_const_step {name : String} {v₁ v₂ : Value}
      : HeadSmallStep V (.letIn name (.value v₁) (.value v₂)) (.value v₂)
  | fun_step {es : List Expr} {ps : List String} {bd : Expr}
      : (h_len : ps.length = es.length)
      → (r = bd.addBindings ps es h_len)
      → HeadSmallStep V (.funCall (.value (.closure ps bd)) es) r

inductive SmallStep : Env → Expr → Expr → Prop where
  | ctx_step (ctx : Ctx) {V : Env}
      : (e₁' = ctx.fill e₁) → (e₂' = ctx.fill e₂)
      → HeadSmallStep (ctx.updateEnv V) e₁ e₂
      → SmallStep V e₁' e₂'

abbrev SmallSteps (env : Env) : Expr → Expr → Prop :=
  Relation.ReflTransGen (SmallStep env)

def SmallSteps.single {env : Env} :
    SmallStep env e₁ e₂ → SmallSteps env e₁ e₂ := by
  intro step
  exact Relation.ReflTransGen.single step
