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

@[simp] lemma nestCtx_preserves_updateEnv (ctx' ctx : Ctx) {V : Env}
  : ctx'.updateEnv (ctx.updateEnv V) = (ctx.fillWithCtx ctx').updateEnv V := by
  induction ctx generalizing V <;> simp_all [Ctx.updateEnv, Ctx.fillWithCtx]

@[simp] lemma nestCtx_preserves_fill (ctx' ctx : Ctx) {e : Expr}
  : ctx.fill (ctx'.fill e) = (ctx.fillWithCtx ctx').fill e := by
  induction ctx <;> simp_all only [Ctx.fill, Ctx.fillWithCtx]

lemma fill_injective {ctx : Ctx}
    : ctx.fill e₁ = ctx.fill e₂ → e₁ = e₂ := by
  induction ctx <;> simp_all

lemma SmallStep.with_ctx (ctx : Ctx)
    : (e₁' = ctx.fill e₁) → (e₂' = ctx.fill e₂)
    → SmallStep defs (ctx.updateEnv V) e₁ e₂ → SmallStep defs V e₁' e₂' := by
  rintro rfl rfl ⟨ctx', rfl, rfl, hstep⟩
  simp only [nestCtx_preserves_updateEnv, nestCtx_preserves_fill] at *
  apply ctx_step <;> trivial

lemma SmallSteps.with_ctx (ctx : Ctx)
    : (e₁' = ctx.fill e₁) → (e₂' = ctx.fill e₂)
    → SmallSteps defs (ctx.updateEnv V) e₁ e₂ → SmallSteps defs V e₁' e₂' := by
  rintro rfl rfl steps
  apply Relation.ReflTransGen.lift ctx.fill ?_ steps
  intro _ _ step
  exact SmallStep.with_ctx ctx rfl rfl step

lemma value_not_redex : IsValue e → ¬Redex e := by rintro ⟨⟩ ⟨⟩

lemma fill_is_value_implies_hole {ctx : Ctx} (is_value : IsValue (ctx.fill e))
    : ctx = .hole := by
  cases ctx
  case hole => rfl
  all_goals cases is_value

lemma fill_is_value_implies_eq {ctx : Ctx} (is_value : IsValue (ctx.fill e))
    : ctx.fill e = e := by
  suffices ctx = .hole by simp [this]
  exact fill_is_value_implies_hole is_value

lemma fill_is_value_implies_value {ctx : Ctx} (is_value : IsValue (ctx.fill e))
    : IsValue e := by
  suffices ctx = .hole by simpa [this] using is_value
  exact fill_is_value_implies_hole is_value

lemma fill_redex_implies_hole_or_value {ctx : Ctx} (redex : Redex (ctx.fill e))
    : ctx = .hole ∨ IsValue e := by
  cases ctx
  case hole => left; rfl
  all_goals
    right
    cases redex
    apply fill_is_value_implies_value
    trivial

lemma fill_redex_redex_implies_hole {ctx : Ctx} (rout : Redex (ctx.fill e)) (rin : Redex e)
    : ctx = .hole := by
  cases fill_redex_implies_hole_or_value rout
  · assumption
  · exfalso
    apply value_not_redex <;> trivial

lemma redex_of_headSmallStep : HeadSmallStep defs V e₁ e₂ → Redex e₁ := by
  rintro ⟨⟩ <;> repeat constructor

lemma fill_redex_injective_in_ctx {ctx₁ ctx₂ : Ctx} (r₁ : Redex e₁) (r₂ : Redex e₂)
    : ctx₁.fill e₁ = ctx₂.fill e₂ → ctx₁ = ctx₂ := by
  intro eq
  induction ctx₂ generalizing ctx₁
  · cases eq
    apply fill_redex_redex_implies_hole <;> assumption
  · rename_i ctx' op' e' ih
    cases ctx₁
    · cases eq
      symm
      apply fill_redex_redex_implies_hole <;> assumption
    · rename_i ctx'' op'' e''
      simp [Ctx.fill] at eq
      rcases eq with ⟨ rfl, eq, rfl ⟩
      have : ctx'' = ctx' := by apply ih; assumption
      rw [this]
    · rename_i n op'' ctx''
      simp [Ctx.fill] at eq
      rcases eq with ⟨ rfl, eq, rfl ⟩
      -- need to show a messy contradiction
      sorry
    · sorry
    · sorry
  · sorry
  · sorry
  · sorry

lemma ctx_and_redex_of_smallStep
    : SmallStep defs V e₁ e₂
    → ∃ (ctx : Ctx), ∃ e₁' e₂', e₁ = ctx.fill e₁' ∧ e₂ = ctx.fill e₂' ∧ Redex e₁' := by
  rintro ⟨ctx, rfl, rfl, step⟩
  rename_i e₁ e₂
  use ctx, e₁, e₂
  and_intros <;> try rfl
  apply redex_of_headSmallStep <;> assumption

lemma no_headSmallStep_from_value {defs : Definitions} (is_value : IsValue v)
    : ¬HeadSmallStep defs V v e := by
  cases is_value
  nofun

lemma no_smallStep_from_value {defs : Definitions} (is_value : IsValue v)
    : ¬SmallStep defs V v e := by
  rintro ⟨ctx, rfl, rfl, step⟩
  apply (no_headSmallStep_from_value ?_ step)
  apply fill_is_value_implies_value
  assumption
