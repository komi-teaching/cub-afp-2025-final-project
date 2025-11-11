import LocalLang.AST
import LocalLang.Semantics
import LocalLang.Types
import LocalLang.Typing

def EnvRespectsCtx (Γ : TypeContext) (V : Env) : Prop :=
  ∀ (x : String) (n : ℕ), V[x]? = some n → (x, .nat) ∈ Γ

-- если тип.nat то это есть в  V, если тип .func, то должно быть в defs : Definitions

-- TODO: prove
-- TODO: V and Γ should be related
theorem preservation (Γ : TypeContext) (e e' : Expr) (ty : LLType) (defs : Definitions)
  : TypeJdg Γ e ty → HeadSmallStep defs V e e' → TypeJdg Γ e' ty := by
  intro h_jdg b
  induction b
  · cases h_jdg
    · rename_i relΓ
      apply TypeJdg.jdgConst
  · cases h_jdg
    · rename_i H₁ H₂
      apply TypeJdg.jdgConst
  · rename_i name val n
    cases h_jdg
    apply TypeJdg.jdgConst
  · cases h_jdg
    sorry

-- Progress: if TypeJdg Γ e ty, then e can take a step.
-- TODO: formalize

-- TODO: Also interesting:
-- if TypeJdg Γ e ty, then eval e succeeds
