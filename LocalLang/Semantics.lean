import LocalLang.AST
import LocalLang.Evaluator
import LocalLang.Ctx
import Mathlib.Logic.Relation

abbrev Env := Std.HashMap String ℕ

-- for rewriting (.funCall f es) in terms of let
def letin_chain (vars : List (String × Expr)) (e : Expr) : Expr :=
  vars.foldl (fun e' (x, xe) => .letIn x xe e') e

inductive SmallStep (defs : Definitions) : Env → Expr → Expr → Prop where
  | var_step : V[x]? = some n →
      SmallStep defs V (.var x) (.const n)
  | bin_op_step {op : BinOp} :
      SmallStep defs V (.binOp op (.const e₁) (.const e₂)) (.const (op.eval e₁ e₂))
  | ctx_step (ctx : Ctx) : SmallStep defs V e₁ e₂ →
      SmallStep defs V (ctx.fill e₁) (ctx.fill e₂)
  | letin_cong {name : String} {val : ℕ} : SmallStep defs (V.insert name val) e₁ e₂ →
      SmallStep defs V (.letIn name (.const val) e₁) (.letIn name (.const val) e₂)
  | letin_const_step {name : String} {val n : ℕ} :
      SmallStep defs V (.letIn name (.const val) (.const n)) (.const n)
  | fun_step {ps : List String} {body : Expr} {es : List Expr}
      (Hf : f ∈ defs) (Hpn : ps.length = es.length) :
      SmallStep defs V (.funCall f es) (letin_chain (defs[f].parameters.zip es) defs[f].body)

abbrev SmallSteps (defs : Definitions) (env : Env) : Expr → Expr → Prop :=
  Relation.ReflTransGen (SmallStep defs env)

def SmallSteps.single {defs : Definitions} {env : Env} :
    SmallStep defs env e₁ e₂ → SmallSteps defs env e₁ e₂ := by
  intro step
  exact Relation.ReflTransGen.single step

-- TODO: prove
theorem smallSteps_diamond {defs : Definitions} {e₁ e₂ e₃ : Expr}
  (HA : SmallSteps defs V e₁ e₂) (HB : SmallSteps defs V e₁ e₃)
  :  ∃ e₄, SmallSteps defs V e₂ e₄ ∧ SmallSteps defs V e₃ e₄ := sorry
