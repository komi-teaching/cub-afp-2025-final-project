import LocalLang.AST
import LocalLang.Semantics
import LocalLang.Types
import LocalLang.Typing

-- TODO: prove
theorem preservation (Γ : TypeContext) (e e' : Expr) (ty : LLType) (defs : Definitions)
  : TypeJdg Γ e ty → SmallStep defs e e' → TypeJdg Γ e' ty := sorry

-- Progress: if TypeJdg Γ e ty, then e can take a step.
-- TODO: formalize

-- TODO: Also interesting:
-- if TypeJdg Γ e ty, then eval e succeeds
