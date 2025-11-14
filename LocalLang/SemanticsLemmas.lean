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

def Ctx.nestCtx (innerCtx : Ctx) : Ctx → Ctx
  | .hole => innerCtx
  | .binOpLhs ctx₀ op e => .binOpLhs (nestCtx innerCtx ctx₀) op e
  | .binOpRhs n op ctx₀ => .binOpRhs n op (nestCtx innerCtx ctx₀)
  | .letInExpr x ctx₀ e => .letInExpr x (nestCtx innerCtx ctx₀) e
  | .letInBody x n ctx₀ => .letInBody x n (nestCtx innerCtx ctx₀)

lemma nestCtx_preserves_updateEnv (ctx' ctx : Ctx) {V : Env}
  : ctx'.updateEnv (ctx.updateEnv V) = (ctx'.nestCtx ctx).updateEnv V := by
  induction ctx generalizing V <;> simp only [Ctx.updateEnv, Ctx.nestCtx] <;> (
    expose_names
    apply a_ih
  )

lemma nestCtx_preserves_fill (ctx' ctx : Ctx) {e : Expr}
  : ctx.fill (ctx'.fill e) = (ctx'.nestCtx ctx).fill e := by
  induction ctx <;> simp [Ctx.fill, Ctx.nestCtx] <;> assumption

lemma SmallStep.with_ctx (ctx : Ctx)
    : (e₁' = ctx.fill e₁) → (e₂' = ctx.fill e₂)
    → SmallStep defs (ctx.updateEnv V) e₁ e₂ → SmallStep defs V e₁' e₂' := by
  intro e₁'_eq e₂'_eq step
  let ⟨ctx', e₁_eq, e₂_eq, hstep⟩ := step
  rename_i e₁_h e₂_h
  rw [nestCtx_preserves_updateEnv ctx' ctx] at hstep
  apply ctx_step (ctx'.nestCtx ctx) ?_ ?_ hstep
  · rw [e₁'_eq, e₁_eq]; apply nestCtx_preserves_fill
  · rw [e₂'_eq, e₂_eq]; apply nestCtx_preserves_fill

lemma SmallSteps.with_ctx (ctx : Ctx)
    : (e₁' = ctx.fill e₁) → (e₂' = ctx.fill e₂)
    → SmallSteps defs (ctx.updateEnv V) e₁ e₂ → SmallSteps defs V e₁' e₂' := by
  intro e₁'_eq e₂'_eq steps
  rw [e₁'_eq, e₂'_eq]
  apply Relation.ReflTransGen.lift (ctx.fill) ?_ steps
  simp
  intro e e' step
  exact SmallStep.with_ctx ctx rfl rfl step

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
