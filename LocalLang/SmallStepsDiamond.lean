import LocalLang.Semantics
import LocalLang.SemanticsLemmas

lemma headSmallStep_from_var_deterministic {defs : Definitions}
  (st : HeadSmallStep defs V (.var x) e)
  : ∃ n, V[x]? = some n ∧ e = .const n := by
  cases st with
  | var_step h_in' =>
    rename_i n
    use n

lemma smallStep_from_var_deterministic {defs : Definitions}
  (st : SmallStep defs V (.var x) e)
  : ∃ n, V[x]? = some n ∧ e = .const n := by
  cases st with
  | ctx_step ctx e₁'_eq e₂'_eq head_st =>
    rename_i e₁ e₂
    rw [e₂'_eq]
    let ⟨ctx_eq, e₁_eq⟩ := var_eq_fill_implies_hole e₁'_eq
    simp only [ctx_eq, Ctx.fill, Ctx.updateEnv] at *
    rw [← e₁_eq] at head_st
    exact headSmallStep_from_var_deterministic head_st

lemma headSmallStep_from_const_binOp_deterministic {defs : Definitions} {op : BinOp}
  (st : HeadSmallStep defs V (.binOp op (.const n₁) (.const n₂)) e)
  : e = .const (op.eval n₁ n₂) := by
  cases st <;> simpa

-- TODO: extract repeating parts
lemma smallStep_from_const_binOp_deterministic {defs : Definitions} {op : BinOp}
  (st : SmallStep defs V (.binOp op (.const n₁) (.const n₂)) e) : e = .const (op.eval n₁ n₂) := by
  cases st with
  | ctx_step ctx e₁'_eq e₂'_eq head_st =>
    rename_i e₁ e₂
    cases ctx <;> try (simp only [Ctx.fill] at *) <;> try contradiction
    case hole =>
      rw [← e₁'_eq, ← e₂'_eq] at head_st
      exact headSmallStep_from_const_binOp_deterministic head_st
    all_goals
      injection e₁'_eq
      rename _ = Ctx.fill e₁ _ => e₁_fill_eq
      let ⟨ctx_eq, e₁_eq⟩ := const_eq_fill_implies_hole e₁_fill_eq
      rw [← e₁_eq] at head_st
      cases no_headSmallStep_from_const head_st

lemma headSmallStep_from_const_letIn_deterministic {defs : Definitions}
  (st : HeadSmallStep defs V (.letIn x (.const n₁) (.const n₂)) e) : e = .const n₂ := by
  cases st
  rfl

lemma smallStep_from_const_letIn_deterministic {defs : Definitions}
  (st : SmallStep defs V (.letIn x (.const n₁) (.const n₂)) e) : e = .const n₂ := by
  cases st with
  | ctx_step ctx e₁'_eq e₂'_eq head_st =>
    rename_i e₁ e₂
    cases ctx <;> try (simp only [Ctx.fill] at *) <;> try contradiction
    case hole =>
      rw [← e₁'_eq, ← e₂'_eq] at head_st
      exact headSmallStep_from_const_letIn_deterministic head_st
    all_goals
      injection e₁'_eq
      rename _ = Ctx.fill e₁ _ => e₁_fill_eq
      let ⟨ctx_eq, e₁_eq⟩ := const_eq_fill_implies_hole e₁_fill_eq
      rw [← e₁_eq] at head_st
      cases no_headSmallStep_from_const head_st

lemma headSmallStep_from_funCall_deterministic {defs : Definitions} {es : List Expr}
  (h_f : f ∈ defs) (st : HeadSmallStep defs V (.funCall f es) e)
    : e = .addBindings (defs[f].parameters.zip es) defs[f].body := by
  cases st with
  | fun_step h_f h_ps h_bd h_r h_len => rw [h_r, h_ps, h_bd]

lemma smallStep_from_funCall_deterministic {defs : Definitions} {es : List Expr}
  (h_f : f ∈ defs) (st : SmallStep defs V (.funCall f es) e)
    : e = .addBindings (defs[f].parameters.zip es) defs[f].body := by
  cases st with
  | ctx_step ctx e₁'_eq e₂'_eq head_st =>
    rename_i e₁ e₂
    cases ctx <;> simp only [Ctx.fill] at * <;> try contradiction
    case hole =>
      rw [← e₁'_eq, ← e₂'_eq] at head_st
      exact headSmallStep_from_funCall_deterministic h_f head_st

lemma headSmallStep_and_smallStep_deterministic {defs : Definitions}
  (h_a : SmallStep defs V e₁ e₂) (h_b : HeadSmallStep defs V e₁ e₃) : e₂ = e₃ := by
  cases h_b with
  | var_step h_in' =>
    let ⟨n, ⟨h_in, e_eq⟩⟩ := smallStep_from_var_deterministic h_a
    rw [h_in'] at h_in
    injection h_in with n_eq
    rw [n_eq, e_eq]
  | bin_op_step n_eq =>
    let result := smallStep_from_const_binOp_deterministic h_a
    rw [← n_eq] at result
    assumption
  | let_in_const_step => exact smallStep_from_const_letIn_deterministic h_a
  | fun_step h_f h_ps h_bd h_r h_len =>
    let result := smallStep_from_funCall_deterministic h_f h_a
    rw [← h_ps, ← h_bd, ← h_r] at result
    assumption

lemma headSmallStep_deterministic {defs : Definitions}
  (h_a : HeadSmallStep defs V e₁ e₂) (h_b : HeadSmallStep defs V e₁ e₃) : e₂ = e₃ :=
  headSmallStep_and_smallStep_deterministic
    (.ctx_step .hole (by rw [Ctx.fill]) (by rw [Ctx.fill]) h_a) h_b

theorem smallStep_deterministic {defs : Definitions}
  (h_a : SmallStep defs V e₁ e₂) (h_b : SmallStep defs V e₁ e₃) : e₂ = e₃ := by
  let ⟨ctx, e₁_eq, e₂_eq, head_st⟩ := h_b
  rename_i e₁' e₂'
  induction ctx generalizing e₁ e₂ e₃ h_a V <;> simp only [Ctx.fill] at *
  case hole =>
    rw [← e₁_eq, ← e₂_eq] at head_st
    exact headSmallStep_and_smallStep_deterministic h_a head_st
  all_goals (
    let ⟨ctx', e₁_eq', e₃_eq, head_st'⟩ := h_a
    rename_i e₁'' e₃'
    rw [e₁_eq] at e₁_eq'
    cases ctx' <;> simp only [Ctx.fill] at e₁_eq' e₃_eq <;> try contradiction
  ) <;> try first
    | rw [← e₁_eq', ← e₃_eq, Ctx.updateEnv] at head_st'
      rw [e₁_eq] at h_b
      exact Eq.symm (headSmallStep_and_smallStep_deterministic h_b head_st')
    | injection e₁_eq' with op'_eq fill_eq e'_eq
      first
      | let ⟨_, e₁'_eq⟩ := const_eq_fill_implies_hole (Eq.symm fill_eq)
        rw [← e₁'_eq] at head_st
        cases no_headSmallStep_from_const head_st
      | let ⟨_, e₁'_eq⟩ := const_eq_fill_implies_hole fill_eq
        rw [← e₁'_eq] at head_st'
        cases no_headSmallStep_from_const head_st'
  case binOpLhs.binOpLhs ctx₀ _ _ ih ctx₀' _ _ =>
    injection e₁_eq' with op'_eq fill_eq e'_eq
    let h_a' := SmallStep.ctx_step ctx₀ (by rfl) (by rfl) head_st
    let h_b' := SmallStep.ctx_step ctx₀' (by rfl) (by rfl) head_st'
    rw [← fill_eq] at h_b'
    let result := ih h_b' h_a' (by rfl) (by rfl) head_st
    rw [e₂_eq, e₃_eq, ← op'_eq, ← e'_eq, result]
  case binOpRhs.binOpRhs _ _ ctx₀ ih _ _ ctx₀' =>
    injection e₁_eq' with op'_eq n_eq fill_eq
    let h_a' := SmallStep.ctx_step ctx₀ (by rfl) (by rfl) head_st
    let h_b' := SmallStep.ctx_step ctx₀' (by rfl) (by rfl) head_st'
    rw [← fill_eq] at h_b'
    let result := ih h_b' h_a' (by rfl) (by rfl) head_st
    rw [e₂_eq, e₃_eq, ← op'_eq, ← n_eq, result]
  case letInExpr.letInExpr _ ctx₀ _ ih _ ctx₀' _ =>
    injection e₁_eq' with x'_eq fill_eq e'_eq
    let h_a' :=SmallStep.ctx_step ctx₀ (by rfl) (by rfl) head_st
    let h_b' := SmallStep.ctx_step ctx₀' (by rfl) (by rfl) head_st'
    rw [← fill_eq] at h_b'
    let result := ih h_b' h_a' (by rfl) (by rfl) head_st
    rw [e₂_eq, e₃_eq, ← x'_eq, ← e'_eq, result]
  case letInBody.letInBody _ _ ctx₀ ih _ _ ctx₀' =>
    injection e₁_eq' with x'_eq n'_eq fill_eq
    injection n'_eq  with n'_eq
    simp only [Ctx.updateEnv] at head_st head_st'
    let h_a' := SmallStep.ctx_step ctx₀ (by rfl) (by rfl) head_st
    let h_b' := SmallStep.ctx_step ctx₀' (by rfl) (by rfl) head_st'
    rw [← fill_eq, ← x'_eq, ← n'_eq] at h_b'
    let result := ih h_b' h_a' (by rfl) (by rfl) head_st
    rw [e₂_eq, e₃_eq, ← x'_eq, ← n'_eq, result]

theorem smallSteps_diamond {defs : Definitions} {e₁ e₂ e₃ : Expr}
  (h_a : SmallSteps defs V e₁ e₂) (h_b : SmallSteps defs V e₁ e₃)
  :  ∃ e₄, SmallSteps defs V e₂ e₄ ∧ SmallSteps defs V e₃ e₄ := by
  let ⟨e₄, _⟩ := Relation.church_rosser (by
    intro a b c st_a st_b
    use c
    let b_eq_c := smallStep_deterministic st_a st_b
    rw [b_eq_c]
    constructor
    · exact Relation.ReflGen.refl
    · exact Relation.ReflTransGen.refl
  ) h_a h_b
  use e₄
