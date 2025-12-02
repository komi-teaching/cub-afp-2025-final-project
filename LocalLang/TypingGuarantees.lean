import LocalLang.AST
import LocalLang.Semantics
import LocalLang.Types
import LocalLang.Typing

def EnvRespectsCtx (Γ : TypeContext) (V : Env) : Prop :=
  ∀ (x : String) (n : ℕ), V[x]? = some n → Γ[x]? = LLType.nat

-- TODO: prove
-- TODO: V and Γ should be related
theorem preservation (Γ : TypeContext) (e e' : Expr) (ty : LLType) (defs : Definitions)
    (h_env_respects : EnvRespectsCtx Γ V)
  : TypeJdg Γ e ty → HeadSmallStep defs V e e' → TypeJdg Γ e' ty := by
  intro h_jdg b
  induction b
  · cases h_jdg
    · rename_i x n a relΓ
      unfold EnvRespectsCtx at h_env_respects
      let ent_ctx_link := h_env_respects x n a
      let symmRelΓ := relΓ.symm
      have ty_eq := Option.some.inj (symmRelΓ.trans ent_ctx_link)
      rw [ty_eq]
      constructor
  · cases h_jdg
    · rename_i H₁ H₂
      apply TypeJdg.jdg_const
  · rename_i name val n
    cases h_jdg
    · rename_i H₁ H₂
      cases H₂
      constructor
  · cases h_jdg
    rename_i f es arg_types T_return h_f h_args
    sorry

-- Progress: if TypeJdg Γ e ty, then e can take a step.
-- TODO: formalize

-- TODO: Also interesting:
-- if TypeJdg Γ e ty, then eval e succeeds
