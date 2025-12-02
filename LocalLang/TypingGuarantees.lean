import LocalLang.AST
import LocalLang.Semantics
import LocalLang.Types
import LocalLang.Typing

def EnvRespectsCtx (Γ : TypeContext) (V : Env) : Prop :=
  ∀ (x : String) (n : ℕ), V[x]? = some n → Γ[x]? = LLType.nat

def CtxRespectsEnv (V : Env) (Γ : TypeContext) : Prop :=
  ∀ x : String, Γ[x]? = some LLType.nat → x ∈ V

def CtxRespectsDefs (Γ : TypeContext) (defs : Definitions) : Prop :=
   (T_ret : LLType) → (arg_types : List LLType) → (f : String) → (f_in_defs : f ∈ defs) →
    (h_type : Γ[f]? = some (LLType.func arg_types T_ret)) →
    (TypeJdg Γ defs[f].body T_ret)


theorem addBindings_typing {ps : List String} {es : List Expr} {bd : Expr}
                                {T_ret : LLType} {arg_types : List LLType}
  {defs : Definitions} (ctxRespectDefs : CtxRespectsDefs Γ defs)
  (f : String) (h_args : Γ[f]? = some (LLType.func arg_types T_ret))
  (f_in_defs : f ∈ defs) (eq_bd_defs : bd = defs[f].body)
  : TypeJdg Γ (Expr.addBindings (ps.zip es) bd) T_ret
    :=
    by
      generalize qs_equality : (ps.zip es) = qs
      induction qs with
      | nil =>
        simp [Expr.addBindings]
        let res := ctxRespectDefs T_ret arg_types f f_in_defs h_args
        rw [eq_bd_defs.symm] at res
        apply res
      | cons head tail ih => sorry


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
    rename_i f es' ps bd f_in_defs a eq_bd_defs es eq arg_types h_f h_args
    simp [es]
    apply addBindings_typing ctx_defs_respects f h_args f_in_defs eq_bd_defs

-- Progress: if TypeJdg Γ e ty, then e can take a step.
-- TODO: formalize

-- TODO: Also interesting:
-- if TypeJdg Γ e ty, then eval e succeeds
