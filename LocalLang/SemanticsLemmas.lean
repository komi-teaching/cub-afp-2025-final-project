import LocalLang.Semantics

variable {defs : Definitions}

instance :
  Trans (SmallStep defs V) (SmallStep defs V) (SmallSteps defs V) where
    trans st₁ st₂ := Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single st₁) (Relation.ReflTransGen.single st₂)

@[simp] lemma addBindings_single {e xe : Expr}
    : e.addBindings [(x, xe)] = Expr.letIn x xe e := by
  simp [Expr.addBindings]

lemma SmallStep.hole_step : HeadSmallStep defs V e₁ e₂ → SmallStep defs V e₁ e₂ := by
  intro hstep
  exact .ctx_step .hole (by rw [Ctx.fill]) (by rw [Ctx.fill]) hstep

lemma nestCtx_preserves_updateEnv (ctx' ctx : Ctx) {V : Env}
  : ctx'.updateEnv (ctx.updateEnv V) = (ctx.fillWithCtx ctx').updateEnv V := by
  induction ctx generalizing V <;> simp only [Ctx.updateEnv, Ctx.fillWithCtx] <;> (
    -- assumption won't work here, since we need to infer the implicit arg {V : Env} of ih
    -- if we use ih as a named hypothesis, V gets inferred automatically
    rename_i ih
    exact ih
  )

lemma nestCtx_preserves_fill (ctx' ctx : Ctx) {e : Expr}
  : ctx.fill (ctx'.fill e) = (ctx.fillWithCtx ctx').fill e := by
  induction ctx <;> simp only [Ctx.fill, Ctx.fillWithCtx] <;> congr

lemma SmallStep.with_ctx (ctx : Ctx)
    : (e₁' = ctx.fill e₁) → (e₂' = ctx.fill e₂)
    → SmallStep defs (ctx.updateEnv V) e₁ e₂ → SmallStep defs V e₁' e₂' := by
  intro e₁'_eq e₂'_eq step
  let ⟨ctx', e₁_eq, e₂_eq, hstep⟩ := step
  rename_i e₁_h e₂_h
  rw [nestCtx_preserves_updateEnv ctx' ctx] at hstep
  apply ctx_step (ctx.fillWithCtx ctx') ?_ ?_ hstep
  · rw [e₁'_eq, e₁_eq]; apply nestCtx_preserves_fill
  · rw [e₂'_eq, e₂_eq]; apply nestCtx_preserves_fill

lemma SmallSteps.with_ctx (ctx : Ctx)
    : (e₁' = ctx.fill e₁) → (e₂' = ctx.fill e₂)
    → SmallSteps defs (ctx.updateEnv V) e₁ e₂ → SmallSteps defs V e₁' e₂' := by
  intro e₁'_eq e₂'_eq steps
  rw [e₁'_eq, e₂'_eq]
  apply Relation.ReflTransGen.lift ctx.fill ?_ steps
  intro e e' step
  exact SmallStep.with_ctx ctx rfl rfl step

lemma var_eq_fill_implies_hole {ctx : Ctx}
  (eq : Expr.var x = ctx.fill e)
  : (ctx = .hole ∧ Expr.var x = e) := by
    cases ctx <;> simp only [Ctx.fill] at eq <;> try contradiction
    constructor
    · rfl
    · assumption

lemma const_eq_fill_implies_hole {ctx : Ctx}
  (eq : Expr.const n = ctx.fill e)
  : (ctx = .hole ∧ Expr.const n = e) := by
    cases ctx <;> simp only [Ctx.fill] at eq <;> try contradiction
    constructor
    · rfl
    · assumption

lemma no_headSmallStep_from_const {defs : Definitions}
  : ¬HeadSmallStep defs V (.const x) e := nofun

lemma no_smallStep_from_const {defs : Definitions}
  : ¬SmallStep defs V (.const x) e := by
    generalize e₀_eq : Expr.const x = e₀ at *
    intro st
    cases st with
    | ctx_step ctx e₁'_eq e₂'_eq headSt =>
      rw [e₁'_eq] at e₀_eq
      let ⟨ctx_eq, e₁_eq⟩ := const_eq_fill_implies_hole e₀_eq
      rw [← e₁_eq] at headSt
      exact no_headSmallStep_from_const headSt
