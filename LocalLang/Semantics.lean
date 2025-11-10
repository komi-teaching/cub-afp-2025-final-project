import LocalLang.AST
import LocalLang.Evaluator
import LocalLang.Ctx
import Mathlib.Logic.Relation
import Mathlib.Tactic.Tauto

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
  | letInConstStep {name : String} {val n : ℕ} :
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

@[simp] lemma var_eq_fill_implies_hole {ctx : Ctx}
  (H : Expr.var x = ctx.fill e)
  : (ctx = .hole) := by
    cases ctx
    any_goals simp [Ctx.fill] at H
    rfl

@[simp] lemma const_eq_fill_implies_hole {ctx : Ctx}
  (H : Expr.const n = ctx.fill e)
  : (ctx = .hole) := by
    cases ctx
    any_goals simp [Ctx.fill] at H
    rfl

@[simp] lemma no_smallStep_from_const {defs : Definitions}
  (st : SmallStep defs V (.const x) e) : False := by
    generalize e₀_eq : Expr.const x = e₀ at *
    induction st <;> try contradiction
    · rename_i ih
      let ctx_eq := const_eq_fill_implies_hole e₀_eq
      simp [ctx_eq, Ctx.fill] at e₀_eq
      apply ih
      assumption

lemma smallStep_with_varStep_deterministic {defs : Definitions}
  (Hin : V[x]? = some n) (st : SmallStep defs V (.var x) e) : (.const n = e) := by
    generalize e₀_eq : Expr.var x = e₀ at *
    induction st <;> try contradiction
    · rename_i x' n' Hin'
      injection e₀_eq with x_eq
      rw [← x_eq, Hin] at Hin'
      injection Hin' with n_eq
      rw [n_eq]
    · rename_i e₁ e₂ ctx V st' ih
      let ctx_eq_hole := var_eq_fill_implies_hole e₀_eq
      simp [ctx_eq_hole, Ctx.fill, Ctx.updateEnv] at *
      simp [ctx_eq_hole, Ctx.fill] at e₀_eq
      exact ih Hin e₀_eq

-- TODO: extract repeating parts
lemma smallStep_with_binOpStep_deterministic {defs : Definitions} {op : BinOp}
  (st : SmallStep defs V (.binOp op (.const n₁) (.const n₂)) e) : (.const (op.eval n₁ n₂) = e) := by
    generalize e₀_eq : Expr.binOp op (.const n₁) (.const n₂) = e₀ at st
    induction st <;> try contradiction
    · injection e₀_eq with op_eq e₁_eq e₂_eq
      injection e₁_eq with n₁_eq
      injection e₂_eq with n₂_eq
      simp [op_eq, n₁_eq, n₂_eq]
    · rename_i e₁ e₂ ctx V' st' ih
      cases ctx <;> try (simp [Ctx.fill] at *)
      · exact ih e₀_eq
      · let n_eq := e₀_eq.right.left
        let ctx_eq := const_eq_fill_implies_hole n_eq
        simp [Ctx.fill, ctx_eq] at st' n_eq
        rw [← n_eq] at st'
        apply no_smallStep_from_const
        assumption
      · let n_eq := e₀_eq.right.right
        let ctx_eq := const_eq_fill_implies_hole n_eq
        simp [Ctx.fill, ctx_eq] at st' n_eq
        rw [← n_eq] at st'
        apply no_smallStep_from_const
        assumption

lemma smallStep_with_letInConstStep_deterministic {defs : Definitions}
  (st : SmallStep defs V (.letIn x (.const n₁) (.const n₂)) e) : (.const n₂ = e) := by
    generalize e₀_eq : Expr.letIn x (.const n₁) (.const n₂) = e₀ at st
    induction st <;> try contradiction
    · rename_i e₁ e₂ ctx V' st' ih
      cases ctx <;> try (simp [Ctx.fill] at *)
      · exact ih e₀_eq
      · let n_eq := e₀_eq.right.left
        let ctx_eq := const_eq_fill_implies_hole n_eq
        simp [Ctx.fill, ctx_eq] at st' n_eq
        rw [← n_eq] at st'
        apply no_smallStep_from_const
        assumption
      · let n_eq := e₀_eq.right.right
        let ctx_eq := const_eq_fill_implies_hole n_eq
        simp [Ctx.fill, ctx_eq] at st' n_eq
        rw [← n_eq] at st'
        apply no_smallStep_from_const
        assumption
    · injection e₀_eq

lemma smallStep_with_funStep_deterministic {defs : Definitions} {es : List Expr}
  (Hf : f ∈ defs) (st : SmallStep defs V (.funCall f es) e)
    : (letin_chain (defs[f].parameters.zip es) defs[f].body = e) := by
      generalize e₀_eq : Expr.funCall f es = e₀ at *
      induction st <;> try contradiction
      · rename_i e₁ e₂ ctx env st' ih
        cases ctx <;> (simp [Ctx.fill] at *)
        · exact ih e₀_eq
      · rename_i f' V' ps' body' es' Hf' Hpn'
        injection e₀_eq with f_eq es_eq
        rw [← es_eq]
        let defs_f_eq : defs[f] = defs[f'] := getElem_congr rfl f_eq Hf
        rw [← defs_f_eq]

lemma ctxStep_with_hole_deterministic {defs : Definitions} {ctx' : Ctx}
  (ih : SmallStep defs V e₁ (ctx'.fill e₂') → e₂ = Ctx.fill e₂' ctx')
  (e₀_eq : e₁ = ctx'.fill e₁')
  (st' : SmallStep defs (Ctx.updateEnv V ctx') e₁' e₂') : ctx'.fill e₂' = e₂ := by
    apply Eq.symm
    apply ih
    rw [e₀_eq]
    exact .ctxStep ctx' V st'

theorem smallStep_deterministic {defs : Definitions}
  (HA : SmallStep defs V e₁ e₂) (HB : SmallStep defs V e₁ e₃) : e₂ = e₃ := by
  induction HA with
  | varStep Hin => exact smallStep_with_varStep_deterministic Hin HB
  | binOpStep => exact smallStep_with_binOpStep_deterministic HB
  | letInConstStep => exact smallStep_with_letInConstStep_deterministic HB
  | funStep Hf Hpn => exact smallStep_with_funStep_deterministic Hf HB
  | ctxStep ctx V st ih => {
    rename_i e₁ e₂
    generalize e₀_eq : Ctx.fill e₁ ctx = e₀ at *
    let HA := SmallStep.ctxStep ctx V st
    cases HB <;> (simp [e₀_eq] at HA; apply Eq.symm)
    · rename_i Hin
      exact smallStep_with_varStep_deterministic Hin HA
    · exact smallStep_with_binOpStep_deterministic HA
    · sorry
    · exact smallStep_with_letInConstStep_deterministic HA
    · expose_names
      exact smallStep_with_funStep_deterministic Hf HA
  }

-- TODO: prove
theorem smallSteps_diamond {defs : Definitions} {e₁ e₂ e₃ : Expr}
  : SmallSteps defs V e₁ e₂ → SmallSteps defs V e₁ e₃ →
    ∃ e₄, SmallSteps defs V e₂ e₄ ∧ SmallSteps defs V e₃ e₄ := by
  intro HA HB
  induction HA : HA generalizing e₃ HB with
  | refl => exists e₃
  | tail asts ast ih => {
      rename_i e₁' e₂' HA
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
