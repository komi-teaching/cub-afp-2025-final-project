import LocalLang.AST
import LocalLang.Semantics
import LocalLang.Types
import LocalLang.Typing

def EnvRespectsCtx (Γ : TypeContext) (V : Env) : Prop :=
  ∀ (x : String) (v : Value), V[x]? = v → ∃ ty, Γ[x]? = some ty ∧ v.TypeJdg ty

def CtxRespectsEnv (V : Env) (Γ : TypeContext) : Prop :=
  ∀ (x : String) (ty : LLType), Γ[x]? = some ty
  → ∃ v, V[x]? = some v ∧ v.TypeJdg ty

theorem addBindings_typing (Γ : TypeContext) (ps : List String) (es : List Expr)
                           (bd : Expr) (ty : LLType)
                           (H_len : ps.length = es.length) (arg_types : List LLType)
  (H_args : Expr.TypeJdgList Γ es arg_types)
  (body_jdg : Expr.TypeJdg Γ (Expr.value (Value.closure ps bd)) (LLType.func arg_types ty))
  : Expr.TypeJdg Γ (Expr.addBindings ps es bd H_len) ty := by
  generalize qs_equality : (ps.zip es) = qs
  induction qs with
  | nil =>
          simp [Expr.addBindings]
          rw [qs_equality]
          simp
          rw [List.zip_eq_nil_iff] at qs_equality
          have h_ps_nil : ps = [] := by
           cases qs_equality with
           | inl h => apply h
           | inr h =>
             rw [h] at H_len
             exact List.eq_nil_of_length_eq_zero H_len
          cases body_jdg with
          | jdg_value h_value =>
            cases h_value with
            | jdg_closure body_jdg' =>
              simp [h_ps_nil] at body_jdg'
              sorry
  | cons head tail ih => sorry


theorem preservation (env : Env) (Γ : TypeContext) (e e' : Expr) (ty : LLType)
    (h_env_respects : EnvRespectsCtx Γ env)
  : Expr.TypeJdg Γ e ty → HeadSmallStep env e e' → Expr.TypeJdg Γ e' ty := by
    intro h_jdg b
    induction b
    · -- const_step
      cases h_jdg
      apply Expr.TypeJdg.jdg_value
      apply Value.TypeJdg.jdg_nat
    · -- var_step
      rename_i env n a relΓ
      cases h_jdg
      unfold EnvRespectsCtx at h_env_respects
      let ent_ctx_link := h_env_respects n a relΓ
      constructor
      rename_i relΓJd
      rcases ent_ctx_link with ⟨ty', H_ty'_in_ctx, H_a_type_jdg⟩
      rw [relΓJd] at H_ty'_in_ctx
      rw [Option.some.inj H_ty'_in_ctx]
      apply H_a_type_jdg
    · -- case bin_op_step
      cases h_jdg
      rename_i H₁ H₂
      cases H₂
      apply Expr.TypeJdg.jdg_value
      apply Value.TypeJdg.jdg_nat
    · -- case let_in_const_step
      cases h_jdg
      apply Expr.TypeJdg.jdg_value
      rename_i H₁ H₂
      cases H₂
      assumption
    · -- case fun_step.jdg_fun
      cases h_jdg
      rename_i r env es ps bd H_len r_eq arg_types H_args f_jdg
      rw [r_eq]
      apply addBindings_typing Γ ps es bd ty H_len arg_types H_args f_jdg
