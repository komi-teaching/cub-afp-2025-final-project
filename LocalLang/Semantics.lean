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

lemma no_headSmallStep_from_const {defs : Definitions}
  (st : HeadSmallStep defs V (.const x) e) : False := by
    cases st

lemma no_smallStep_from_const {defs : Definitions}
  (st : SmallStep defs V (.const x) e) : False := by
    generalize e₀_eq : Expr.const x = e₀ at *
    cases st with
    | ctx_step ctx e₁'_eq e₂'_eq headSt => {
      rw [e₁'_eq] at e₀_eq
      let ⟨ctx_eq, e₁_eq⟩ := const_eq_fill_implies_hole e₀_eq
      rw [← e₁_eq] at headSt
      apply no_headSmallStep_from_const headSt
    }

lemma headSmallStep_from_var_deterministic {defs : Definitions}
  (Hin : V[x]? = some n) (st : HeadSmallStep defs V (.var x) e) : (.const n = e) := by
    cases st with
    | var_step Hin' => {
      rename_i n'
      rw [Hin'] at Hin
      injection Hin with n'_eq_n
      simp [n'_eq_n]
    }

lemma smallStep_from_var_deterministic {defs : Definitions}
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
      exact headSmallStep_from_var_deterministic Hin headSt
    }

lemma headSmallStep_from_const_binOp_deterministic {defs : Definitions} {op : BinOp}
  (st : HeadSmallStep defs V (.binOp op (.const n₁) (.const n₂)) e)
  : (.const (op.eval n₁ n₂) = e) := by
    cases st with
    | bin_op_step n_eq => simp only [n_eq]

-- TODO: extract repeating parts
lemma smallStep_from_const_binOp_deterministic {defs : Definitions} {op : BinOp}
  (st : SmallStep defs V (.binOp op (.const n₁) (.const n₂)) e) : (.const (op.eval n₁ n₂) = e) := by
    generalize e₀_eq : Expr.binOp op (.const n₁) (.const n₂) = e₀ at st
    cases st with
    | ctx_step ctx e₁'_eq e₂'_eq headSt => {
      rename_i e₁ e₂
      simp [e₁'_eq] at e₀_eq
      cases ctx <;> try simp [Ctx.fill] at *
      case hole => (
        rw [← e₀_eq, ← e₂'_eq] at headSt
        exact headSmallStep_from_const_binOp_deterministic headSt
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

lemma headSmallStep_from_const_letIn_deterministic {defs : Definitions}
  (st : HeadSmallStep defs V (.letIn x (.const n₁) (.const n₂)) e) : (.const n₂ = e) := by
    cases st
    · rfl

lemma smallStep_from_const_letIn_deterministic {defs : Definitions}
  (st : SmallStep defs V (.letIn x (.const n₁) (.const n₂)) e) : (.const n₂ = e) := by
    generalize e₀_eq : Expr.letIn x (.const n₁) (.const n₂) = e₀ at st
    cases st with
    | ctx_step ctx e₁'_eq e₂'_eq headSt => {
      rename_i e₁ e₂
      rw [e₁'_eq] at e₀_eq
      cases ctx <;> try (simp [Ctx.fill] at *)
      case hole => (
        rw [← e₀_eq, ← e₂'_eq] at headSt
        exact headSmallStep_from_const_letIn_deterministic headSt
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

lemma headSmallStep_from_funCall_deterministic {defs : Definitions} {es : List Expr}
  (Hf : f ∈ defs) (st : HeadSmallStep defs V (.funCall f es) e)
    : (.addBindings (defs[f].parameters.zip es) defs[f].body = e) := by
      cases st with
      | fun_step h_f Hps Hbd Hr Hlen => rw [Hr, Hps, Hbd]

lemma smallStep_from_funCall_deterministic {defs : Definitions} {es : List Expr}
  (Hf : f ∈ defs) (st : SmallStep defs V (.funCall f es) e)
    : (.addBindings (defs[f].parameters.zip es) defs[f].body = e) := by
      generalize e₀_eq : Expr.funCall f es = e₀ at *
      cases st with
      | ctx_step ctx e₁'_eq e₂'_eq headSt => {
        rename_i e₁ e₂
        rw [e₁'_eq] at e₀_eq
        cases ctx <;> try (simp [Ctx.fill] at *)
        case hole => (
          rw [← e₀_eq, ← e₂'_eq] at headSt
          exact headSmallStep_from_funCall_deterministic Hf headSt
        )
      }

lemma headSmallStep_and_smallStep_deterministic {defs : Definitions}
  (HA : HeadSmallStep defs V e₁ e₂) (HB : SmallStep defs V e₁ e₃) : e₂ = e₃ := by
    cases HA with
    | var_step Hin' => exact smallStep_from_var_deterministic Hin' HB
    | bin_op_step n_eq => {
      let result := smallStep_from_const_binOp_deterministic HB
      rw [← n_eq] at result
      assumption
    }
    | let_in_const_step => exact smallStep_from_const_letIn_deterministic HB
    | fun_step h_f Hps Hbd Hr Hlen => {
      let result := smallStep_from_funCall_deterministic h_f HB
      rw [← Hps, ← Hbd, ← Hr] at result
      assumption
    }

lemma headSmallStep_deterministic {defs : Definitions}
  (HA : HeadSmallStep defs V e₁ e₂) (HB : HeadSmallStep defs V e₁ e₃) : e₂ = e₃ :=
    headSmallStep_and_smallStep_deterministic HA
      (.ctx_step .hole (by rw [Ctx.fill]) (by rw [Ctx.fill]) HB)

-- TODO: prove
theorem smallStep_deterministic {defs : Definitions}
  (HA : SmallStep defs V e₁ e₂) (HB : SmallStep defs V e₁ e₃) : e₂ = e₃ := by
  let ⟨ctx, e₁_eq, e₂_eq, headSt⟩ := HA
  rename_i e₁' e₂'
  induction ctx generalizing e₁ e₂ e₃ HB V <;> simp [Ctx.fill] at *
  case hole => (
    rw [← e₁_eq, ← e₂_eq] at headSt
    exact headSmallStep_and_smallStep_deterministic headSt HB
  )
  case binOpLhs ctx₀ op' e' ih => (
    let ⟨ctx', e₁_eq', e₃_eq, headSt'⟩ := HB
    rename_i e₁'' e₃'
    rw [e₁_eq] at e₁_eq'
    cases ctx' <;> simp [Ctx.fill] at e₁_eq' e₃_eq
    case hole => (
      rw [← e₁_eq', ← e₃_eq, Ctx.updateEnv] at headSt'
      rw [e₁_eq] at HA
      exact Eq.symm (headSmallStep_and_smallStep_deterministic headSt' HA)
    )
    case binOpLhs ctx₀' op'' e'' => (
      let ⟨op'_eq, ⟨fill_eq, e'_eq⟩⟩ := e₁_eq'
      let HA' : SmallStep defs V (ctx₀.fill e₁') (ctx₀.fill e₂')
        := SmallStep.ctx_step ctx₀ (by rfl) (by rfl) headSt
      let HB' : SmallStep defs V (ctx₀'.fill e₁'') (ctx₀'.fill e₃')
        := SmallStep.ctx_step ctx₀' (by rfl) (by rfl) headSt'
      rw [← fill_eq] at HB'
      let result := ih HA' HB' (by rfl) (by rfl) headSt
      rw [e₂_eq, e₃_eq, ← op'_eq, ← e'_eq, result]
    )
    case binOpRhs n op'' ctx₀' => (
      let ⟨op'_eq, ⟨fill_eq, e'_eq⟩⟩ := e₁_eq'
      let ⟨_, e₁'_eq⟩ := const_eq_fill_implies_hole (Eq.symm fill_eq)
      rw [← e₁'_eq] at headSt
      let : False := no_headSmallStep_from_const headSt
      contradiction
    )
  )
  case binOpRhs n op' ctx₀ ih => (
    let ⟨ctx', e₁_eq', e₃_eq, headSt'⟩ := HB
    rename_i e₁'' e₃'
    rw [e₁_eq] at e₁_eq'
    cases ctx' <;> simp [Ctx.fill] at e₁_eq' e₃_eq
    case hole => (
      rw [← e₁_eq', ← e₃_eq, Ctx.updateEnv] at headSt'
      rw [e₁_eq] at HA
      exact Eq.symm (headSmallStep_and_smallStep_deterministic headSt' HA)
    )
    case binOpLhs ctx₀' op'' e'' => (
      let ⟨op'_eq, ⟨fill_eq, e'_eq⟩⟩ := e₁_eq'
      let ⟨_, e₁'_eq⟩ := const_eq_fill_implies_hole fill_eq
      rw [← e₁'_eq] at headSt'
      let : False := no_headSmallStep_from_const headSt'
      contradiction
    )
    case binOpRhs n op'' ctx₀' => (
      let ⟨op'_eq, ⟨n_eq, fill_eq⟩⟩ := e₁_eq'
      let HA' : SmallStep defs V (ctx₀.fill e₁') (ctx₀.fill e₂')
        := SmallStep.ctx_step ctx₀ (by rfl) (by rfl) headSt
      let HB' : SmallStep defs V (ctx₀'.fill e₁'') (ctx₀'.fill e₃')
        := SmallStep.ctx_step ctx₀' (by rfl) (by rfl) headSt'
      rw [← fill_eq] at HB'
      let result := ih HA' HB' (by rfl) (by rfl) headSt
      rw [e₂_eq, e₃_eq, ← op'_eq, ← n_eq, result]
    )
  )
  case letInExpr x' ctx₀ e' ih => (
    let ⟨ctx', e₁_eq', e₃_eq, headSt'⟩ := HB
    rename_i e₁'' e₃'
    rw [e₁_eq] at e₁_eq'
    cases ctx' <;> simp [Ctx.fill] at e₁_eq' e₃_eq
    case hole => (
      rw [← e₁_eq', ← e₃_eq, Ctx.updateEnv] at headSt'
      rw [e₁_eq] at HA
      exact Eq.symm (headSmallStep_and_smallStep_deterministic headSt' HA)
    )
    case letInExpr x'' ctx₀' e'' => (
      let ⟨x'_eq, ⟨fill_eq, e'_eq⟩⟩ := e₁_eq'
      let HA' : SmallStep defs V (ctx₀.fill e₁') (ctx₀.fill e₂')
        := SmallStep.ctx_step ctx₀ (by rfl) (by rfl) headSt
      let HB' : SmallStep defs V (ctx₀'.fill e₁'') (ctx₀'.fill e₃')
        := SmallStep.ctx_step ctx₀' (by rfl) (by rfl) headSt'
      rw [← fill_eq] at HB'
      let result := ih HA' HB' (by rfl) (by rfl) headSt
      rw [e₂_eq, e₃_eq, ← x'_eq, ← e'_eq, result]
    )
    case letInBody x'' n ctx₀' => (
      let ⟨x'_eq, ⟨fill_eq, e'_eq⟩⟩ := e₁_eq'
      let ⟨_, e₁'_eq⟩ := const_eq_fill_implies_hole (Eq.symm fill_eq)
      rw [← e₁'_eq] at headSt
      let : False := no_headSmallStep_from_const headSt
      contradiction
    )
  )
  case letInBody x' n ctx₀ ih => (
    let ⟨ctx', e₁_eq', e₃_eq, headSt'⟩ := HB
    rename_i e₁'' e₃'
    rw [e₁_eq] at e₁_eq'
    cases ctx' <;> simp [Ctx.fill] at e₁_eq' e₃_eq
    case hole => (
      rw [← e₁_eq', ← e₃_eq, Ctx.updateEnv] at headSt'
      rw [e₁_eq] at HA
      exact Eq.symm (headSmallStep_and_smallStep_deterministic headSt' HA)
    )
    case letInExpr x'' ctx₀' e' => (
      let ⟨x'_eq, ⟨fill_eq, e'_eq⟩⟩ := e₁_eq'
      let ⟨_, e₁'_eq⟩ := const_eq_fill_implies_hole fill_eq
      rw [← e₁'_eq] at headSt'
      let : False := no_headSmallStep_from_const headSt'
      contradiction
    )
    case letInBody x'' n' ctx₀' => (
      let ⟨x'_eq, ⟨n'_eq, fill_eq⟩⟩ := e₁_eq'
      simp [Ctx.updateEnv] at headSt headSt'
      let HA' : SmallStep defs _ (ctx₀.fill e₁') (ctx₀.fill e₂')
        := .ctx_step ctx₀ (by rfl) (by rfl) headSt
      let HB' : SmallStep defs _ (ctx₀'.fill e₁'') (ctx₀'.fill e₃')
        := .ctx_step ctx₀' (by rfl) (by rfl) headSt'
      rw [← fill_eq, ← x'_eq, ← n'_eq] at HB'
      let result := ih HA' HB' (by rfl) (by rfl) headSt
      rw [e₂_eq, e₃_eq, ← x'_eq, ← n'_eq, result]
    )
  )

theorem smallSteps_diamond {defs : Definitions} {e₁ e₂ e₃ : Expr}
  (HA : SmallSteps defs V e₁ e₂) (HB : SmallSteps defs V e₁ e₃)
  :  ∃ e₄, SmallSteps defs V e₂ e₄ ∧ SmallSteps defs V e₃ e₄ := by
    let ⟨e₄, _⟩ := Relation.church_rosser (by
      intro a b c st_A st_B
      use c
      let b_eq_c := smallStep_deterministic st_A st_B
      rw [b_eq_c]
      constructor
      · exact Relation.ReflGen.refl
      · exact Relation.ReflTransGen.refl
    ) HA HB
    use e₄
