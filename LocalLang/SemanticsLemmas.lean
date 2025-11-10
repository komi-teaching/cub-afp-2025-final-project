import LocalLang.Semantics

instance {defs : Definitions} :
  Trans (SmallStep defs V) (SmallStep defs V) (SmallSteps defs V) where
    trans st₁ st₂ := Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single st₁) (Relation.ReflTransGen.single st₂)

lemma head_step_implies_context_step {e₁ e₂ e₁' e₂' : Expr} {V V' : Env} {defs : Definitions}
  (st : HeadSmallStep defs V' e₁ e₂) (ctx : Ctx) (HEnv : V' = ctx.updateEnv V)
  (He₁ : e₁' = ctx.fill e₁) (He₂ : e₂' = ctx.fill e₂) : SmallStep defs V e₁' e₂' := by
  rw [HEnv] at st
  let result := SmallStep.ctx_step ctx V st
  rw [← He₁, ← He₂] at result
  assumption

lemma steps_in_context_imply_steps_in_expr {e₁ e₂ e₁' e₂' : Expr} {V V' : Env} {defs : Definitions}
  (sts : SmallSteps defs V' e₁ e₂) (ctx : Ctx) (HEnv : V' = ctx.updateEnv V)
  (He₁ : e₁' = ctx.fill e₁) (He₂ : e₂' = ctx.fill e₂) : SmallSteps defs V e₁' e₂' := by sorry
