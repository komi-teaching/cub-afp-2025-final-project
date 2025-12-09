import LocalLang.AST
import LocalLang.Semantics
import LocalLang.Types
import LocalLang.Typing

def EnvRespectsCtx (Γ : TypeContext) (V : Env) : Prop := sorry

def CtxRespectsEnv (V : Env) (Γ : TypeContext) : Prop :=
  ∀ (x : String) (ty : LLType), Γ[x]? = some ty
  → ∃ v, V[x]? = some v ∧ v.TypeJdg ty

inductive IsFuncType : LLType → Prop where
  | func {param_tys ret_ty} : IsFuncType (.func param_tys ret_ty)

-- TODO: prove
theorem preservation (Γ : TypeContext) (e e' : Expr) (ty : LLType)
    (h_env_respects : EnvRespectsCtx Γ V)
  : Expr.TypeJdg Γ e ty → HeadSmallStep V e e' → Expr.TypeJdg Γ e' ty := sorry

-- Progress: if TypeJdg Γ e ty, then e can take a step.
-- TODO: formalize

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
  | value : IsValue (.value v)

inductive IsRedex : Expr → Prop where
  | const : IsRedex (.const n)
  | var : IsRedex (.var x)
  | binOp {op} : IsRedex (.binOp op (.value v₁) (.value v₂))
  | letInConst : IsRedex (.letIn x (.value v₁) (.value v₂))
  | funCall {es} : IsRedex (.funCall (.value v) es)

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
    | inl lhs_const =>
      cases lhs_const
      rename_i v₁
      cases ih_rhs with
      | inl rhs_const =>
        cases rhs_const
        rename_i v₂
        apply HasDecomposition.decomposition (.binOp op (Expr.value v₁) (Expr.value v₂))
          .hole (by simp)
        constructor
      | inr rhs_dec =>
        let ⟨e', ctx, e_eq, e'_redex⟩ := rhs_dec
        apply HasDecomposition.decomposition e' (.binOpRhs v₁ op ctx) (by simp [e_eq])
        assumption
    | inr lhs_dec =>
      let ⟨e', ctx, e_eq, e'_redex⟩ := lhs_dec
      apply HasDecomposition.decomposition e' (.binOpLhs ctx op rhs) (by simp [e_eq])
      assumption
  · intro name e₁ e₂ ih_e₁ ih_e₂
    apply Or.intro_right
    cases ih_e₁ with
    | inl e₁_const =>
      cases e₁_const
      rename_i v₁
      cases ih_e₂ with
      | inl e₂_const =>
        cases e₂_const
        rename_i v₂
        apply HasDecomposition.decomposition (Expr.letIn name (Expr.value v₁) (Expr.value v₂))
          .hole (by simp)
        constructor
      | inr e₂_dec =>
        let ⟨e', ctx, e_eq, e'_redex⟩ := e₂_dec
        apply HasDecomposition.decomposition e' (.letInBody name v₁ ctx) (by simp [e_eq])
        assumption
    | inr e₁_dec =>
      let ⟨e', ctx, e_eq, e'_redex⟩ := e₁_dec
      apply HasDecomposition.decomposition e' (.letInExpr name ctx e₂) (by simp [e_eq])
      assumption
  · intro f es ih_f ih_es
    apply Or.intro_right
    cases ih_f
    · rename_i f_value
      cases f_value
      rename_i v
      apply HasDecomposition.decomposition ((Expr.value v).funCall es) .hole (by simp)
      constructor
    · rename_i f_dec
      let ⟨e', ctx, fill_eq, e'_redex⟩ := f_dec
      apply HasDecomposition.decomposition e' (.funCallBody ctx es) (by simp [fill_eq])
      assumption

lemma redex_progress : ∀ {Γ e ty}, Expr.TypeJdg Γ e ty → IsRedex e →
  CtxRespectsEnv V Γ → ∃ e', HeadSmallStep V e e' := by
  intro Γ e ty e_jdg e_redex V_resp_Γ
  cases e_redex with
  | const =>
    rename_i n
    exists .value (.nat n)
    constructor
  | var =>
    cases e_jdg
    rename_i x x_ty
    let ⟨v, ⟨v_in_V, v_jdg⟩⟩ := V_resp_Γ x ty x_ty
    exists .value v
    constructor
    assumption
  | binOp =>
    cases e_jdg with
    | jdg_binOp e₁_jdg e₂_jdg =>
      rename_i v₁ v₂ op
      cases e₁_jdg
      cases e₂_jdg
      rename_i v₁_jdg v₂_jdg
      cases v₁_jdg
      cases v₂_jdg
      rename_i n₁ n₂
      exists .value (.nat (op.eval n₁ n₂))
      apply HeadSmallStep.bin_op_step rfl
  | letInConst =>
    rename_i x v₁ v₂
    exists .value v₂
    constructor
  | funCall =>
    rename_i v es
    cases e_jdg with
    | jdg_fun f_jdg es_jdg =>
      rename_i arg_tys ret_ty
      cases f_jdg
      rename_i v_jdg
      cases v_jdg
      rename_i ps bd ps_jdg
      exists bd.addBindings ps es sorry
      apply HeadSmallStep.fun_step sorry rfl

theorem progress {Γ : TypeContext} {ty : LLType}
  : Expr.TypeJdg Γ e ty → CtxRespectsEnv V Γ →
    IsValue e ∨ ∃ e', SmallStep V e e' := by
  intro e_jdg V_ext_Γ

  sorry

-- TODO: Also interesting:
-- if TypeJdg Γ e ty, then eval e succeeds
