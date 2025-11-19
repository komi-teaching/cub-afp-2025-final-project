import LocalLang.AST
import LocalLang.Evaluator
import LocalLang.Ctx
import Mathlib.Logic.Relation

inductive HeadSmallStep (defs : Definitions) : Env → Expr → Expr → Prop where
  | var_step : V[x]? = some n →
      HeadSmallStep defs V (.var x) (.const n)
  | bin_op_step {op : BinOp}
      : n = op.eval e₁ e₂
      → HeadSmallStep defs V (.binOp op (.const e₁) (.const e₂)) (.const n)
  | let_in_const_step {name : String} {n₁ n₂ : ℕ}
      : HeadSmallStep defs V (.letIn name (.const n₁) (.const n₂)) (.const n₂)
  | fun_step {f : String} {es : List Expr} {ps : List String} {bd : Expr}
      : (h_f : f ∈ defs)
      → (ps = defs[f].parameters)
      → (bd = defs[f].body)
      → (r = bd.addBindings (ps.zip es))
      → (ps.length = es.length)
      → HeadSmallStep defs V (.funCall f es) r

inductive SmallStep (defs : Definitions) : Env → Expr → Expr → Prop where
  | ctx_step (ctx : Ctx) {V : Env}
      : (e₁' = ctx.fill e₁) → (e₂' = ctx.fill e₂)
      → HeadSmallStep defs (ctx.updateEnv V) e₁ e₂
      → SmallStep defs V e₁' e₂'

abbrev SmallSteps (defs : Definitions) (env : Env) : Expr → Expr → Prop :=
  Relation.ReflTransGen (SmallStep defs env)

def SmallSteps.single {defs : Definitions} {env : Env} :
    SmallStep defs env e₁ e₂ → SmallSteps defs env e₁ e₂ := by
  intro step
  exact Relation.ReflTransGen.single step
