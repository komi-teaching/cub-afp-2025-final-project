import LocalLang.Semantics

variable {defs : Definitions}

instance :
  Trans (SmallStep defs V) (SmallStep defs V) (SmallSteps defs V) where
    trans st₁ st₂ := Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single st₁) (Relation.ReflTransGen.single st₂)

@[simp] lemma addBindings_single {e xe : Expr}
    : e.addBindings [(x, xe)] = Expr.letIn x xe e := by sorry

lemma SmallStep.hole_step : HeadSmallStep defs V e₁ e₂ → SmallStep defs V e₁ e₂ := by sorry

lemma SmallStep.with_ctx (ctx : Ctx)
    : (e₁' = ctx.fill e₁) → (e₂' = ctx.fill e₂)
    → SmallStep defs (ctx.updateEnv V) e₁ e₂ → SmallStep defs V e₁' e₂' := by sorry

lemma SmallSteps.with_ctx (ctx : Ctx)
    : (e₁' = ctx.fill e₁) → (e₂' = ctx.fill e₂)
    → SmallSteps defs (ctx.updateEnv V) e₁ e₂ → SmallSteps defs V e₁' e₂' := by sorry

lemma var_eq_fill_implies_hole {ctx : Ctx}
  (H : Expr.var x = ctx.fill e)
  : (ctx = .hole ∧ Expr.var x = e) := by
    cases ctx
    any_goals simp [Ctx.fill] at H
    constructor
    · rfl
    · assumption

lemma const_eq_fill_implies_hole {ctx : Ctx}
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
