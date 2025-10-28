import LocalLang.AST

-- TODO: define
inductive SmallStep (defs : Definitions) : Expr → Expr → Prop where

-- TODO: define
inductive SmallSteps (defs : Definitions) : Expr → Expr → Prop where

-- TODO: prove
theorem smallSteps_diamond {defs : Definitions} {e₁ e₂ e₃ : Expr}
  (HA : SmallSteps defs e₁ e₂) (HB : SmallSteps defs e₁ e₃)
  :  ∃ e₄, SmallSteps defs e₂ e₄ ∧ SmallSteps defs e₃ e₄ := sorry
