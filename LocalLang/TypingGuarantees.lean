import LocalLang.AST
import LocalLang.Semantics
import LocalLang.Types
import LocalLang.Typing
import LocalLang.Weakening

namespace TypeContext

def respects_env (Γ : TypeContext) (V : Env) : Prop :=
  ∀ (x : String) (v : Value), V[x]? = v → ∃ ty, Γ[x]? = some ty ∧ v.TypeJdg ty

end TypeContext

namespace Env

def respects_type_context (V : Env) (Γ : TypeContext) : Prop :=
  ∀ (x : String) (ty : LLType), Γ[x]? = some ty
  → ∃ v, V[x]? = some v ∧ v.TypeJdg ty

end Env

theorem addBindings_typing (Γ : TypeContext) {ps : List String} {es : List Expr}
                           (bd : Expr) (ty : LLType)
                           (H_len : ps.length = es.length) (arg_types : List LLType)
  (H_args : Expr.TypeJdgList Γ es arg_types)
  (body_jdg : Expr.TypeJdg Γ (Expr.value (Value.closure ps bd)) (LLType.func arg_types ty))
  : Expr.TypeJdg Γ (Expr.addBindings ps es bd H_len) ty := by

  cases body_jdg with
  | jdg_value h_val =>
    cases h_val with
    | jdg_closure h_body_raw h_len_eq =>
      have h_body_gen : Expr.TypeJdg (TypeContext.union Γ (Std.HashMap.ofList (ps.zip arg_types))) bd ty := by
         apply weakening_expr
         · apply TypeContext.subset_union_right
         · exact h_body_raw
      clear h_body_raw

      generalize qs_eq : (ps.zip es) = qs

      induction qs generalizing ps es bd arg_types with
      | nil =>
        unfold Expr.addBindings
        rw [qs_eq]
        rw [List.zip_eq_nil_iff] at qs_eq
        cases qs_eq with
        | inl h_ps_nil =>
           rw [h_ps_nil] at h_body_gen
           simp at h_body_gen
           simp
           rw [TypeContext.union_empty] at h_body_gen
           exact h_body_gen
        | inr h =>
           rw [h] at H_len
           have := List.eq_nil_of_length_eq_zero H_len
           subst ps
           simp at h_body_gen
           simp
           rw [TypeContext.union_empty] at h_body_gen
           exact h_body_gen

      | cons head tail ih =>
        cases ps with
        | nil => simp at qs_eq
        | cons p ps' =>
          cases es with
          | nil => simp at qs_eq
          | cons e es' =>
             rw [List.zip_cons_cons, List.cons.injEq] at qs_eq
             have h_head : (p, e) = head := qs_eq.left
             have h_tail : ps'.zip es' = tail := qs_eq.right

             cases H_args with
             | cons h_e_typed h_es_typed =>
                rename_i head_arg_type tail_arg_types
                unfold Expr.addBindings
                rw [List.zip_cons_cons, List.foldl_cons]
                have H_len' : ps'.length = es'.length := by
                  simpa [List.length] using H_len

                apply ih (ps := ps') (es := es') (bd := Expr.letIn p e bd)
                         (H_len := H_len') (arg_types := tail_arg_types)
                · exact h_es_typed
                · simpa [List.length] using h_len_eq
                · apply Expr.TypeJdg.jdg_let_in (ty₁ := head_arg_type)
                  · apply weakening_expr
                    · apply TypeContext.subset_union_left
                      sorry
                    · exact h_e_typed
                  · rw [List.zip_cons_cons, TypeContext.union_cons] at h_body_gen
                    exact h_body_gen
                · exact h_tail

theorem preservation (env : Env) (Γ : TypeContext) (e e' : Expr) (ty : LLType)
    (h_env_respects : Γ.respects_env env)
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
      unfold TypeContext.respects_env at h_env_respects
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
      apply addBindings_typing Γ bd ty H_len arg_types H_args f_jdg
