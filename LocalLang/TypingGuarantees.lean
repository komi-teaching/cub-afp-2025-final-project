import LocalLang.AST
import LocalLang.Semantics
import LocalLang.Types
import LocalLang.Typing

def EnvRespectsCtx (Γ : TypeContext) (V : Env) : Prop :=
  ∀ (x : String) (n : ℕ), V[x]? = some n → (x, .nat) ∈ Γ


-- I want to link Definitions with Γ, every name only one time
-- def DefsRespectsCtx (Γ : TypeContext) (defs : Definitions) : Prop :=
--   ∀ (name : String) (ty : LLType) (f : Function),
--     (name, ty) ∈ Γ ∧ defs[name]? = some f →
--     TypeJdg Γ _ ty

lemma is_uniquely_typed {Γ : TypeContext} {k : String} {t₁ t₂ : LLType} :
  (k, t₁) ∈ Γ → (k, t₂) ∈ Γ → t₁ = t₂ := by
    sorry

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
      let is_uniq := is_uniquely_typed relΓ ent_ctx_link
      rw [is_uniq]
      constructor
  · cases h_jdg
    · rename_i H₁ H₂
      apply TypeJdg.jdgConst
  · rename_i name val n
    cases h_jdg
    · rename_i H₁ H₂
      cases H₂
      constructor
  · cases h_jdg
    sorry

-- Progress: if TypeJdg Γ e ty, then e can take a step.
-- TODO: formalize

-- TODO: Also interesting:
-- if TypeJdg Γ e ty, then eval e succeeds
