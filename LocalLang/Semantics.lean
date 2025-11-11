import LocalLang.AST
import LocalLang.Evaluator
import LocalLang.Ctx
import Mathlib.Logic.Relation

-- for rewriting (.funCall f es) in terms of let
def Expr.addBindings (vars : List (String × Expr)) (e : Expr) : Expr :=
  vars.foldl (fun e' (x, xe) => .letIn x xe e') e

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

@[simp] lemma var_eq_fill_implies_hole {ctx : Ctx}
  (H : Expr.var x = ctx.fill e)
  : (ctx = .hole ∧ Expr.var x = e) := by
    cases ctx
    any_goals simp [Ctx.fill] at H
    constructor
    · rfl
    · assumption

@[simp] lemma const_eq_fill_implies_hole {ctx : Ctx}
  (H : Expr.const n = ctx.fill e)
  : (ctx = .hole ∧ Expr.const n = e) := by
    cases ctx
    any_goals simp [Ctx.fill] at H
    constructor
    · rfl
    · assumption

@[simp] lemma no_headSmallStep_from_const {defs : Definitions}
  (st : HeadSmallStep defs V (.const x) e) : False := by
    cases st

@[simp] lemma no_smallStep_from_const {defs : Definitions}
  (st : SmallStep defs V (.const x) e) : False := by
    generalize e₀_eq : Expr.const x = e₀ at *
    cases st with
    | ctx_step ctx e₁'_eq e₂'_eq headSt => {
      rw [e₁'_eq] at e₀_eq
      let ⟨ctx_eq, e₁_eq⟩ := const_eq_fill_implies_hole e₀_eq
      rw [← e₁_eq] at headSt
      apply no_headSmallStep_from_const headSt
    }

lemma smallStep_with_varStep_deterministic {defs : Definitions}
  (Hin : V[x]? = some n) (st : SmallStep defs V (.var x) e) : (.const n = e) := by
    generalize e₀_eq : Expr.var x = e₀ at *
    cases st with
    | ctx_step ctx e₁'_eq e₂'_eq headSt => {
      rename_i e₁ e₂
      rw [e₁'_eq] at e₀_eq
      rw [e₂'_eq]
      let ⟨ctx_eq, e₁_eq⟩ := var_eq_fill_implies_hole e₀_eq
      simp [ctx_eq, Ctx.fill, Ctx.updateEnv] at *
      rw [← e₁_eq] at headSt
      cases headSt with
      | var_step Hin' => {
        rename_i n'
        rw [Hin'] at Hin
        injection Hin with n'_eq_n
        simp [n'_eq_n]
      }
    }

lemma headSmallStep_with_binOpStep_deterministic {defs : Definitions} {op : BinOp}
  (st : HeadSmallStep defs V (.binOp op (.const n₁) (.const n₂)) e)
  : (.const (op.eval n₁ n₂) = e) := by
    cases st with
    | bin_op_step n_eq => simp only [n_eq]

-- TODO: extract repeating parts
lemma smallStep_with_binOpStep_deterministic {defs : Definitions} {op : BinOp}
  (st : SmallStep defs V (.binOp op (.const n₁) (.const n₂)) e) : (.const (op.eval n₁ n₂) = e) := by
    generalize e₀_eq : Expr.binOp op (.const n₁) (.const n₂) = e₀ at st
    cases st with
    | ctx_step ctx e₁'_eq e₂'_eq headSt => {
      rename_i e₁ e₂
      simp [e₁'_eq] at e₀_eq
      cases ctx <;> try simp [Ctx.fill] at *
      case hole => (
        rw [← e₀_eq, ← e₂'_eq] at headSt
        exact headSmallStep_with_binOpStep_deterministic headSt
      )
      case binOpLhs ctx₀ op' e' => (
        let ⟨op_eq, ⟨e₁_fill_eq, e_eq⟩⟩ := e₀_eq
        let ⟨ctx_eq, e₁_eq⟩ := const_eq_fill_implies_hole e₁_fill_eq
        rw [← e₁_eq] at headSt
        let : False := no_headSmallStep_from_const headSt
        contradiction
      )
      case binOpRhs n op' ctx₀ => (
        let ⟨op_eq, ⟨n_eq, e₁_fill_eq⟩⟩ := e₀_eq
        let ⟨ctx_eq, e₁_eq⟩ := const_eq_fill_implies_hole e₁_fill_eq
        rw [← e₁_eq] at headSt
        let : False := no_headSmallStep_from_const headSt
        contradiction
      )
    }

lemma headSmallStep_with_letInConstStep_deterministic {defs : Definitions}
  (st : HeadSmallStep defs V (.letIn x (.const n₁) (.const n₂)) e) : (.const n₂ = e) := by
    cases st
    · rfl

lemma smallStep_with_letInConstStep_deterministic {defs : Definitions}
  (st : SmallStep defs V (.letIn x (.const n₁) (.const n₂)) e) : (.const n₂ = e) := by
    generalize e₀_eq : Expr.letIn x (.const n₁) (.const n₂) = e₀ at st
    cases st with
    | ctx_step ctx e₁'_eq e₂'_eq headSt => {
      rename_i e₁ e₂
      rw [e₁'_eq] at e₀_eq
      cases ctx <;> try (simp [Ctx.fill] at *)
      case hole => (
        rw [← e₀_eq, ← e₂'_eq] at headSt
        exact headSmallStep_with_letInConstStep_deterministic headSt
      )
      case letInExpr x' ctx₀ e' => (
        let ⟨op_eq, ⟨e₁_fill_eq, e_eq⟩⟩ := e₀_eq
        let ⟨ctx_eq, e₁_eq⟩ := const_eq_fill_implies_hole e₁_fill_eq
        rw [← e₁_eq] at headSt
        let : False := no_headSmallStep_from_const headSt
        contradiction
      )
      case letInBody x' n ctx₀ => (
        let ⟨op_eq, ⟨n_eq, e₁_fill_eq⟩⟩ := e₀_eq
        let ⟨ctx_eq, e₁_eq⟩ := const_eq_fill_implies_hole e₁_fill_eq
        rw [← e₁_eq] at headSt
        let : False := no_headSmallStep_from_const headSt
        contradiction
      )
    }

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

lemma head_small_step_and_small_step_deterministic {defs : Definitions}
  (HA : SmallStep defs V e₁ e₂) (HB : HeadSmallStep defs V e₁ e₃) : e₂ = e₃ := by
    sorry

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
  (HA : SmallSteps defs V e₁ e₂) (HB : SmallSteps defs V e₁ e₃)
  :  ∃ e₄, SmallSteps defs V e₂ e₄ ∧ SmallSteps defs V e₃ e₄ := sorry
