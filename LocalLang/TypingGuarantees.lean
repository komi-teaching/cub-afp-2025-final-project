import LocalLang.AST
import LocalLang.Semantics
import LocalLang.Types
import LocalLang.Typing
import LocalLang.Weakening
import LocalLang.TypingLemmas

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
  generalize qs_equality : (ps.zip es) = qs
  induction qs generalizing ps es bd arg_types with
  | nil =>
          rw [Expr.addBindings, qs_equality]
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
              rw [h_ps_nil] at body_jdg'
              apply weakening_expr (empty_subcontext Γ) body_jdg'
  | cons head tail ih =>
    cases ps with
    | nil => simp at qs_equality
    | cons p ps' =>
      cases es with
      | nil => simp at qs_equality
      | cons e es' =>
          rw [List.zip_cons_cons, List.cons.injEq] at qs_equality
          have h_head : (p, e) = head := qs_equality.left
          have h_tail : ps'.zip es' = tail := qs_equality.right
          have H_len' : ps'.length = es'.length := by
                  simpa [List.length] using H_len

          unfold Expr.addBindings
          simp [List.foldl_cons]

          change Expr.TypeJdg Γ (Expr.addBindings ps' es' (Expr.letIn p e bd) H_len') ty
          cases H_args with
          | cons h_e_t h_es' =>
            rename_i head_arg_type arg_types
            cases body_jdg with
            | jdg_value body_jdg' =>
              cases body_jdg' with
              | jdg_closure H_body_jdg H_len_all =>
                apply ih
                · exact h_es'
                · apply Expr.TypeJdg.jdg_value
                  apply Value.TypeJdg.jdg_closure
                  · have h_zip : (p :: ps').zip (head_arg_type :: arg_types)
                      = (p, head_arg_type) :: (ps'.zip arg_types) := rfl
                    rw [h_zip] at H_body_jdg
                    apply Expr.TypeJdg.jdg_let_in (ty₁ := head_arg_type)
                    · apply weakening_expr _ h_e_t
                      sorry
                    · sorry
                  · simp [List.length] at H_len_all
                    exact H_len_all
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

def Expr.simple_rec.{l} {motive : Expr → Sort l}
     (value_case : ∀ v, motive (.value v))
     (const_case : ∀ n, motive (.const n))
     (var_case : ∀ x, motive (.var x))
     (bin_op_case : ∀ op lhs rhs, motive lhs → motive rhs → motive (.binOp op lhs rhs))
     (let_in_case : ∀ name e₁ e₂, motive e₁ → motive e₂ → motive (.letIn name e₁ e₂))
     (fun_case : ∀ f es, motive f → (∀ e', e' ∈ es → motive e') → motive (.funCall f es))
    : (e : Expr) → motive e := go
where go
  | .value v => value_case v
  | .const n => const_case n
  | .var x => var_case x
  | .binOp op lhs rhs => bin_op_case op lhs rhs (go lhs) (go rhs)
  | .letIn name e₁ e₂ => let_in_case name e₁ e₂ (go e₁) (go e₂)
  | .funCall f es => fun_case f es (go f) (fun e' _ => go e')

inductive IsValue : Expr → Prop where
  | value v : IsValue (.value v)

inductive IsRedex : Expr → Prop where
  | const n : IsRedex (.const n)
  | var x : IsRedex (.var x)
  | binOp op v₁ v₂ : IsRedex (.binOp op (.value v₁) (.value v₂))
  | letInValue x v₁ v₂ : IsRedex (.letIn x (.value v₁) (.value v₂))
  | funCall v es : IsRedex (.funCall (.value v) es)

inductive HasDecomposition : Expr → Prop where
  | decomposition (e' : Expr) (ctx : Ctx) : e = ctx.fill e' → IsRedex e' → HasDecomposition e

lemma is_value_or_has_decomposition : ∀ e : Expr, IsValue e ∨ HasDecomposition e := by
  intro e
  apply e.simple_rec
  · intro v
    apply Or.intro_left
    constructor
  · intro n
    apply Or.intro_right
    apply HasDecomposition.decomposition (.const n) .hole (by simp)
    constructor
  · intro x
    apply Or.intro_right
    apply HasDecomposition.decomposition (.var x) .hole (by simp)
    constructor
  · intro op lhs rhs ih_lhs ih_rhs
    apply Or.intro_right
    cases ih_lhs with
    | inl lhs_value =>
      rcases lhs_value with ⟨v₁⟩
      cases ih_rhs with
      | inl rhs_value =>
        rcases rhs_value with ⟨v₂⟩
        apply HasDecomposition.decomposition (.binOp op (Expr.value v₁) (Expr.value v₂))
          .hole (by simp)
        constructor
      | inr rhs_dec =>
        rcases rhs_dec with ⟨e', ctx, e_eq, e'_redex⟩
        apply HasDecomposition.decomposition e' (.binOpRhs v₁ op ctx) (by simp [e_eq])
        assumption
    | inr lhs_dec =>
      rcases lhs_dec with ⟨e', ctx, e_eq, e'_redex⟩
      apply HasDecomposition.decomposition e' (.binOpLhs ctx op rhs) (by simp [e_eq])
      assumption
  · intro name e₁ e₂ ih_e₁ ih_e₂
    apply Or.intro_right
    cases ih_e₁ with
    | inl e₁_value =>
      rcases e₁_value with ⟨v₁⟩
      cases ih_e₂ with
      | inl e₂_value =>
        rcases e₂_value with ⟨v₂⟩
        apply HasDecomposition.decomposition (Expr.letIn name (Expr.value v₁) (Expr.value v₂))
          .hole (by simp)
        constructor
      | inr e₂_dec =>
        rcases e₂_dec with ⟨e', ctx, e_eq, e'_redex⟩
        apply HasDecomposition.decomposition e' (.letInBody name v₁ ctx) (by simp [e_eq])
        assumption
    | inr e₁_dec =>
      rcases e₁_dec with ⟨e', ctx, e_eq, e'_redex⟩
      apply HasDecomposition.decomposition e' (.letInExpr name ctx e₂) (by simp [e_eq])
      assumption
  · intro f es ih_f ih_es
    apply Or.intro_right
    cases ih_f with
    | inl f_value =>
      rcases f_value with ⟨v⟩
      apply HasDecomposition.decomposition ((Expr.value v).funCall es) .hole (by simp)
      constructor
    | inr f_dec =>
      rcases f_dec with ⟨e', ctx, fill_eq, e'_redex⟩
      apply HasDecomposition.decomposition e' (.funCallBody ctx es) (by simp [fill_eq])
      assumption

lemma redex_progress : ∀ {Γ e ty}, Expr.TypeJdg Γ e ty → IsRedex e →
  Env.respectsTypeContext V Γ → ∃ e', HeadSmallStep V e e' := by
  intro Γ e ty e_jdg e_redex V_resp_Γ
  cases e_redex with
  | const n =>
    exists .value (.nat n)
    constructor
  | var x =>
    cases e_jdg
    rename_i x_ty
    let ⟨v, ⟨v_in_V, v_jdg⟩⟩ := V_resp_Γ x ty x_ty
    exists .value v
    constructor
    assumption
  | binOp op v₁ v₂ =>
    cases e_jdg with
    | jdg_binOp e₁_jdg e₂_jdg =>
      -- For some reason, writing ⟨⟨⟨n₁⟩⟩, ⟨⟨n₂⟩⟩⟩ doesn't bind n₁ and n₂ to newly introduced
      -- hypotheses, so I had to do a separate rename_i.
      rcases e₁_jdg, e₂_jdg with ⟨⟨⟨⟩⟩, ⟨⟨⟩⟩⟩
      rename_i n₁ n₂
      exists .value (.nat (op.eval n₁ n₂))
      apply HeadSmallStep.bin_op_step rfl
  | letInValue x v₁ v₂ =>
    exists .value v₂
    constructor
  | funCall v es =>
    cases e_jdg with
    | jdg_fun f_jdg es_jdg =>
      rename_i arg_tys
      -- Same as above
      rcases f_jdg with ⟨⟨⟩⟩
      rename_i ps bd ps_argtys_len_eq ps_jdg
      let ps_es_len_eq : ps.length = es.length := by
        trans arg_tys.length
        · assumption
        · exact len_eq_of_typeJdgList es arg_tys es_jdg
      exists bd.addBindings ps es ps_es_len_eq
      apply HeadSmallStep.fun_step ps_es_len_eq rfl

lemma ctx_fill_tyJdg_implies_original_tyJdg {ty ctx} {V : Env} : Expr.TypeJdg Γ e ty →
  V.respectsTypeContext Γ → e = Ctx.fill e₀ ctx →
  ∃ Γ₀ ty₀, (ctx.updateEnv V).respectsTypeContext Γ₀ ∧ Expr.TypeJdg Γ₀ e₀ ty₀ := by
  intro e_jdg V_resp_Γ fill_eq
  induction ctx generalizing Γ V e e₀ ty <;> (
    rw [fill_eq, Ctx.fill] at e_jdg
    rw [Ctx.fill] at fill_eq
  )
  case hole => exists Γ, ty
  all_goals (
    cases e_jdg
    rename ∀ _ _ _ _ _, _ => ih
    try exact ih (by assumption) V_resp_Γ rfl
  )
  rename_i x v ctx x_ty x_jdg body_jdg
  apply ih body_jdg ?_ rfl
  cases x_jdg
  exact insert_preserves_env_respectsTypeContext V_resp_Γ (by assumption)

theorem progress {Γ : TypeContext} {ty : LLType}
  : Expr.TypeJdg Γ e ty → Env.respectsTypeContext V Γ →
    IsValue e ∨ ∃ e', SmallStep V e e' := by
  intro e_jdg V_resp_Γ
  cases is_value_or_has_decomposition e with
  | inl e_value =>
    apply Or.intro_left
    assumption
  | inr e_dec =>
    apply Or.intro_right
    rcases e_dec with ⟨e₀, ctx, fill_eq, e₀_redex⟩
    let ⟨Γ₀, ty₀, ⟨V'_resp_Γ₀, e₀_jdg⟩⟩ :=
      ctx_fill_tyJdg_implies_original_tyJdg e_jdg V_resp_Γ fill_eq
    let ⟨e₀', e₀_hstep⟩ := redex_progress e₀_jdg e₀_redex V'_resp_Γ₀
    exists ctx.fill e₀'
    exact SmallStep.ctx_step ctx fill_eq rfl e₀_hstep

-- TODO: Also interesting:
-- if TypeJdg Γ e ty, then eval e succeeds
