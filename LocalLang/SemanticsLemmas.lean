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
