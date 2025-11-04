import LocalLang.AST
import LocalLang.Evaluator
import LocalLang.Ctx
import Mathlib.Logic.Relation

-- for rewriting (.funCall f es) in terms of let
def letin_chain (vars : List (String × Expr)) (e : Expr) : Expr :=
  vars.foldl (fun e' (x, xe) => .letIn x xe e') e

inductive SmallStep (defs : Definitions) : Env → Expr → Expr → Prop where
  | varStep : V[x]? = some n →
      SmallStep defs V (.var x) (.const n)
  | binOpStep {op : BinOp} :
      SmallStep defs V (.binOp op (.const e₁) (.const e₂)) (.const (op.eval e₁ e₂))
  | ctxStep (ctx : Ctx) (V : Env) : SmallStep defs (ctx.updateEnv V) e₁ e₂ →
      SmallStep defs V (ctx.fill e₁) (ctx.fill e₂)
  | letinConstStep {name : String} {val n : ℕ} :
      SmallStep defs V (.letIn name (.const val) (.const n)) (.const n)
  | funStep {ps : List String} {body : Expr} {es : List Expr}
      (Hf : f ∈ defs) (Hpn : ps.length = es.length) :
      SmallStep defs V (.funCall f es) (letin_chain (defs[f].parameters.zip es) defs[f].body)

abbrev SmallSteps (defs : Definitions) (env : Env) : Expr → Expr → Prop :=
  Relation.ReflTransGen (SmallStep defs env)

def SmallSteps.single {defs : Definitions} {env : Env} :
    SmallStep defs env e₁ e₂ → SmallSteps defs env e₁ e₂ := by
  intro step
  exact Relation.ReflTransGen.single step

theorem smallStep_deterministic {defs : Definitions}
  (HA : SmallStep defs V e₁ e₂) (HB : SmallStep defs V e₁ e₃) : e₂ = e₃ := by cases e₁ with
  | const n => sorry
  | var x => sorry
  | binOp op e₁ e₂ => sorry
  | letIn x e₁ e₂ => sorry
  | funCall f es => sorry

-- TODO: prove
theorem smallSteps_diamond {defs : Definitions} {e₁ e₂ e₃ : Expr}
  : SmallSteps defs V e₁ e₂ → SmallSteps defs V e₁ e₃ →
    ∃ e₄, SmallSteps defs V e₂ e₄ ∧ SmallSteps defs V e₃ e₄ := by
  intro HA HB
  induction HA : HA generalizing e₃ HB with
  | refl => exists e₃
  | tail asts ast ih => {
      rename_i e₁' e₂' e₃'
      cases HB with
      | refl => {
        exists e₂'
      }
      | tail bsts bst => {
        rename_i e₁''
        let ⟨e₄, ⟨asts', bsts'⟩⟩ := ih asts bsts (by rfl)
        sorry
      }
  }
