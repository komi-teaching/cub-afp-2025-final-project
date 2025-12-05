import LocalLang.AST
import LocalLang.Semantics
import LocalLang.Types
import LocalLang.Typing

def EnvRespectsCtx (Γ : TypeContext) (V : Env) : Prop := sorry

-- TODO: prove
-- TODO: V and Γ should be related
theorem preservation (Γ : TypeContext) (e e' : Expr) (ty : LLType)
    (h_env_respects : EnvRespectsCtx Γ V)
  : Expr.TypeJdg Γ e ty → HeadSmallStep V e e' → Expr.TypeJdg Γ e' ty := sorry

-- Progress: if TypeJdg Γ e ty, then e can take a step.
-- TODO: formalize

-- TODO: Also interesting:
-- if TypeJdg Γ e ty, then eval e succeeds
