import LocalLang.Semantics
import LocalLang.SemanticsLemmas

variable {ps : List String} {bd : Expr}

lemma headSmallStep_from_const_deterministic
  (st : HeadSmallStep V (.const n) e)
  : e = .value (.nat n) := by
  cases st
  rfl

lemma smallStep_from_const_deterministic
  (st : SmallStep V (.const n) e)
  : e = .value (.nat n) := by
  cases st with
  | ctx_step ctx e₁'_eq e₂'_eq head_st =>
    rename_i e₁ e₂
    let ⟨ctx_eq, e₁_eq⟩ := const_eq_fill_implies_hole e₁'_eq
    simp only [ctx_eq, Ctx.fill] at e₂'_eq
    rw [← e₁_eq, ← e₂'_eq] at head_st
    exact headSmallStep_from_const_deterministic head_st

lemma headSmallStep_from_var_deterministic
  (st : HeadSmallStep V (.var x) e)
  : ∃ v, V[x]? = some v ∧ e = .value v := by
  cases st with
  | var_step h_in' =>
    rename_i v
    use v

lemma smallStep_from_var_deterministic
  (st : SmallStep V (.var x) e)
  : ∃ v, V[x]? = some v ∧ e = .value v := by
  cases st with
  | ctx_step ctx e₁'_eq e₂'_eq head_st =>
    rename_i e₁ e₂
    rw [e₂'_eq]
    let ⟨ctx_eq, e₁_eq⟩ := var_eq_fill_implies_hole e₁'_eq
    simp only [ctx_eq, Ctx.fill, Ctx.updateEnv] at *
    rw [← e₁_eq] at head_st
    exact headSmallStep_from_var_deterministic head_st

lemma headSmallStep_from_value_binOp_deterministic {op : BinOp}
  (st : HeadSmallStep V (.binOp op (.value (.nat n₁)) (.value (.nat n₂))) e)
  : e = .value (.nat (op.eval n₁ n₂)) := by
  cases st <;> simp

-- TODO: extract repeating parts
lemma smallStep_from_value_binOp_deterministic {op : BinOp}
  (st : SmallStep V (.binOp op (.value (.nat n₁)) (.value (.nat n₂))) e)
  : e = .value (.nat (op.eval n₁ n₂)) := by
  cases st with
  | ctx_step ctx e₁'_eq e₂'_eq head_st =>
    rename_i e₁ e₂
    cases ctx <;> try (simp only [Ctx.fill] at *) <;> try contradiction
    case hole =>
      rw [← e₁'_eq, ← e₂'_eq] at head_st
      exact headSmallStep_from_value_binOp_deterministic head_st
    all_goals
      injection e₁'_eq
      rename _ = Ctx.fill e₁ _ => e₁_fill_eq
      let ⟨ctx_eq, e₁_eq⟩ := value_eq_fill_implies_hole e₁_fill_eq
      rw [← e₁_eq] at head_st
      cases no_headSmallStep_from_val head_st

lemma headSmallStep_from_const_letIn_deterministic
  (st : HeadSmallStep V (.letIn x (.value v₁) (.value v₂)) e) : e = .value v₂ := by
  cases st
  rfl

lemma smallStep_from_const_letIn_deterministic
  (st : SmallStep V (.letIn x (.value v₁) (.value v₂)) e) : e = .value v₂ := by
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
      let ⟨ctx_eq, e₁_eq⟩ := value_eq_fill_implies_hole e₁_fill_eq
      rw [← e₁_eq] at head_st
      cases no_headSmallStep_from_val head_st

lemma headSmallStep_from_funCall_deterministic {es : List Expr}
  (st : HeadSmallStep V (.funCall (.value (.closure ps bd)) es) e)
  : ∃ (h_len : ps.length = es.length), e = .addBindings ps es bd h_len := by
  cases st with
  | fun_step h_len e_eq =>
    use h_len

lemma smallStep_from_funCall_deterministic {es : List Expr}
  (st : SmallStep V (.funCall (.value (.closure ps bd)) es) e)
  : ∃ (h_len : ps.length = es.length), e = .addBindings ps es bd h_len := by
  cases st with
  | ctx_step ctx e₁'_eq e₂'_eq head_st =>
    rename_i e₁ e₂
    cases ctx <;> simp only [Ctx.fill] at * <;> try contradiction
    case hole =>
      rw [← e₁'_eq, ← e₂'_eq] at head_st
      exact headSmallStep_from_funCall_deterministic head_st
    case funCallBody ctx es =>
      injection e₁'_eq with fill_eq es_eq
      let ⟨ctx_eq, e₁_eq⟩ := value_eq_fill_implies_hole fill_eq
      rw [ctx_eq, Ctx.fill] at fill_eq
      rw [← fill_eq] at head_st
      cases head_st

lemma headSmallStep_and_smallStep_deterministic
  (h_a : SmallStep V e₁ e₂) (h_b : HeadSmallStep V e₁ e₃) : e₂ = e₃ := by
  cases h_b with
  | const_step => exact smallStep_from_const_deterministic h_a
  | var_step h_in' =>
    let ⟨n, ⟨h_in, e_eq⟩⟩ := smallStep_from_var_deterministic h_a
    rw [h_in'] at h_in
    injection h_in with n_eq
    rw [n_eq, e_eq]
  | bin_op_step n_eq => exact smallStep_from_value_binOp_deterministic h_a
  | let_in_const_step => exact smallStep_from_const_letIn_deterministic h_a
  | fun_step h_len h_r =>
    let ⟨_, e₂_eq⟩ := smallStep_from_funCall_deterministic h_a
    rw [← h_r] at e₂_eq
    assumption

lemma headSmallStep_deterministic
  (h_a : HeadSmallStep V e₁ e₂) (h_b : HeadSmallStep V e₁ e₃) : e₂ = e₃ :=
  headSmallStep_and_smallStep_deterministic
    (.ctx_step .hole (by rw [Ctx.fill]) (by rw [Ctx.fill]) h_a) h_b

theorem smallStep_deterministic
  (h_a : SmallStep V e₁ e₂) (h_b : SmallStep V e₁ e₃) : e₂ = e₃ := by
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
      | let ⟨_, e₁'_eq⟩ := value_eq_fill_implies_hole (Eq.symm fill_eq)
        rw [← e₁'_eq] at head_st
        cases no_headSmallStep_from_val head_st
      | let ⟨_, e₁'_eq⟩ := value_eq_fill_implies_hole fill_eq
        rw [← e₁'_eq] at head_st'
        cases no_headSmallStep_from_val head_st'
  case binOpLhs.binOpLhs ctx₀ _ _ ih ctx₀' _ _ =>
    injection e₁_eq' with op'_eq fill_eq e'_eq
    let h_a' := SmallStep.ctx_step ctx₀ rfl rfl head_st
    let h_b' := SmallStep.ctx_step ctx₀' rfl rfl head_st'
    rw [← fill_eq] at h_b'
    let result := ih h_b' h_a' rfl rfl head_st
    rw [e₂_eq, e₃_eq, ← op'_eq, ← e'_eq, result]
  case binOpRhs.binOpRhs _ _ ctx₀ ih _ _ ctx₀' =>
    injection e₁_eq' with op'_eq n_eq fill_eq
    let h_a' := SmallStep.ctx_step ctx₀ rfl rfl head_st
    let h_b' := SmallStep.ctx_step ctx₀' rfl rfl head_st'
    rw [← fill_eq] at h_b'
    let result := ih h_b' h_a' rfl rfl head_st
    rw [e₂_eq, e₃_eq, ← op'_eq, ← n_eq, result]
  case letInExpr.letInExpr _ ctx₀ _ ih _ ctx₀' _ =>
    injection e₁_eq' with x'_eq fill_eq e'_eq
    let h_a' := SmallStep.ctx_step ctx₀ rfl rfl head_st
    let h_b' := SmallStep.ctx_step ctx₀' rfl rfl head_st'
    rw [← fill_eq] at h_b'
    let result := ih h_b' h_a' rfl rfl head_st
    rw [e₂_eq, e₃_eq, ← x'_eq, ← e'_eq, result]
  case letInBody.letInBody _ _ ctx₀ ih _ _ ctx₀' =>
    injection e₁_eq' with x'_eq n'_eq fill_eq
    injection n'_eq  with n'_eq
    simp only [Ctx.updateEnv] at head_st head_st'
    let h_a' := SmallStep.ctx_step ctx₀ rfl rfl head_st
    let h_b' := SmallStep.ctx_step ctx₀' rfl rfl head_st'
    rw [← fill_eq, ← x'_eq, ← n'_eq] at h_b'
    let result := ih h_b' h_a' rfl rfl head_st
    rw [e₂_eq, e₃_eq, ← x'_eq, ← n'_eq, result]
  case funCallBody.funCallBody ctx₀ es ih ctx₀' es' =>
    injection e₁_eq' with e₁'_eq es_eq
    simp only [Ctx.updateEnv] at head_st head_st'
    rw [← es_eq] at e₃_eq
    let h_a' := SmallStep.ctx_step ctx₀ rfl rfl head_st
    let h_b' := SmallStep.ctx_step ctx₀' rfl rfl head_st'
    rw [← e₁'_eq] at h_b'
    let result := ih h_b' h_a' rfl rfl head_st
    rw [e₃_eq, e₂_eq, result]

theorem smallSteps_diamond {e₁ e₂ e₃ : Expr}
  (h_a : SmallSteps V e₁ e₂) (h_b : SmallSteps V e₁ e₃)
  :  ∃ e₄, SmallSteps V e₂ e₄ ∧ SmallSteps V e₃ e₄ := by
  suffices Relation.Join (SmallSteps V) e₂ e₃ by
    let ⟨e₄, _⟩ := this
    use e₄
  apply Relation.church_rosser ?_ h_a h_b
  intro a b c st_a st_b
  use c
  let b_eq_c := smallStep_deterministic st_a st_b
  rw [b_eq_c]
  constructor
  · exact Relation.ReflGen.refl
  · exact Relation.ReflTransGen.refl
