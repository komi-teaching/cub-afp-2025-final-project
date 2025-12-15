import LocalLang.AST
import LocalLang.Semantics
import LocalLang.Types
import LocalLang.Typing

def EnvRespectsCtx (Γ : TypeContext) (V : Env) : Prop :=
  ∀ (x : String) (v : Value), V[x]? = v → ∃ ty, Γ[x]? = some ty ∧ v.TypeJdg ty

def CtxRespectsEnv (V : Env) (Γ : TypeContext) : Prop :=
  ∀ (x : String) (ty : LLType), Γ[x]? = some ty
  → ∃ v, V[x]? = some v ∧ v.TypeJdg ty

def TypeContext.subcontext (Γ₁ Γ₂ : TypeContext) : Prop :=
  ∀ (name : String) (ty : LLType), Γ₁[name]? = some ty → Γ₂[name]? = some ty

theorem subcontext_insert {Γ₁ Γ₂ : TypeContext} {name : String} {ty : LLType}
    (h : TypeContext.subcontext Γ₁ Γ₂) :
    TypeContext.subcontext (Γ₁.insert name ty) (Γ₂.insert name ty) := by
    simp [TypeContext.subcontext]
    intro name_x ty_x lookup_x
    if h_eq : name_x = name then
    subst h_eq
    rw [lookup_x.symm]
    simp
    else
    sorry

mutual
  theorem weakening_expr {Γ₁ Γ₂ : TypeContext} {e : Expr} {ty : LLType}
        (H_sub : TypeContext.subcontext Γ₁ Γ₂)
        (H_jdg : Expr.TypeJdg Γ₁ e ty)
        : Expr.TypeJdg Γ₂ e ty := by
    match H_jdg with
    | .jdg_value h_val => exact Expr.TypeJdg.jdg_value h_val
    | .jdg_var h_lookup => apply Expr.TypeJdg.jdg_var
                           rename_i name
                           exact H_sub name ty h_lookup
    | .jdg_const => constructor
    | .jdg_fun f_jdg H_args => apply Expr.TypeJdg.jdg_fun
                               · exact weakening_expr H_sub f_jdg
                               · exact weakening_list H_sub H_args
    | .jdg_binOp H₁ H₂ => apply Expr.TypeJdg.jdg_binOp
                          · exact weakening_expr H_sub H₁
                          · exact weakening_expr H_sub H₂
    | .jdg_let_in H₁ H₂ => apply Expr.TypeJdg.jdg_let_in
                           · exact weakening_expr H_sub H₁
                           · apply weakening_expr (subcontext_insert H_sub) H₂

theorem weakening_list {Γ₁ Γ₂ : TypeContext} {es : List Expr} {tys : List LLType}
        (H_sub : TypeContext.subcontext Γ₁ Γ₂)
        (H_jdg : Expr.TypeJdgList Γ₁ es tys)
        : Expr.TypeJdgList Γ₂ es tys := by
    match H_jdg with
    | .nil => constructor
    | .cons h_e h_es => exact Expr.TypeJdgList.cons (weakening_expr H_sub h_e) (weakening_list H_sub h_es)

theorem Empty_subcontext (Γ : TypeContext) : TypeContext.subcontext {} Γ
    := by simp [TypeContext.subcontext]

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
              apply weakening_expr (Empty_subcontext Γ) body_jdg'
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
