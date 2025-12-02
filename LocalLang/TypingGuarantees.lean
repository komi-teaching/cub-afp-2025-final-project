import LocalLang.AST
import LocalLang.Semantics
import LocalLang.Types
import LocalLang.Typing

def EnvRespectsCtx (Γ : TypeContext) (V : Env) : Prop :=
  ∀ (x : String) (n : ℕ), V[x]? = some n → Γ[x]? = LLType.nat

def CtxRespectsEnv (V : Env) (Γ : TypeContext) : Prop :=
  ∀ x : String, Γ[x]? = some LLType.nat → x ∈ V

inductive IsFuncType : LLType → Prop where
  | func {param_tys ret_ty} : IsFuncType (.func param_tys ret_ty)

def CtxRespectsDefs (defs : Definitions) (Γ : TypeContext) : Prop :=
  ∀ f : String, (f_in_Γ : f ∈ Γ) → IsFuncType Γ[f] →
  f ∈ defs

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

def Expr.simple_rec.{l} {motive : Expr → Sort l}
     (const_case : ∀ n, motive (.const n))
     (var_case : ∀ x, motive (.var x))
     (bin_op_case : ∀ op lhs rhs, motive lhs → motive rhs → motive (.binOp op lhs rhs))
     (let_in_case : ∀ name e₁ e₂, motive e₁ → motive e₂ → motive (.letIn name e₁ e₂))
     (fun_case : ∀ f es, (∀ e', e' ∈ es → motive e') → motive (.funCall f es))
    : (e : Expr) → motive e := go
where go
  | .const n => const_case n
  | .var x => var_case x
  | .binOp op lhs rhs => bin_op_case op lhs rhs (go lhs) (go rhs)
  | .letIn name e₁ e₂ => let_in_case name e₁ e₂ (go e₁) (go e₂)
  | .funCall f es => fun_case f es (fun e' _ => go e')

inductive IsConst : Expr → Prop where
  | const : IsConst (.const n)

inductive IsRedex : Expr → Prop where
  | var : IsRedex (.var x)
  | binOp {op} : IsRedex (.binOp op (.const n₁) (.const n₂))
  | letInConst : IsRedex (.letIn x (.const n₁) (.const n₂))
  | funCall {es} : IsRedex (.funCall f es)

inductive HasDecomposition : Expr → Prop where
  | decomposition (e' : Expr) (ctx : Ctx) : e = ctx.fill e' → IsRedex e' → HasDecomposition e

lemma is_const_or_has_decomposition : ∀ e : Expr, IsConst e ∨ HasDecomposition e := by
  intro e
  apply e.simple_rec
  · intro n
    apply Or.intro_left
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
      rename_i n₁
      cases ih_rhs with
      | inl rhs_const =>
        cases rhs_const
        rename_i n₂
        apply HasDecomposition.decomposition (.binOp op (Expr.const n₁) (Expr.const n₂))
          .hole (by simp)
        constructor
      | inr rhs_dec =>
        let ⟨e', ctx, e_eq, e'_redex⟩ := rhs_dec
        apply HasDecomposition.decomposition e' (.binOpRhs n₁ op ctx) (by simp [e_eq])
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
      rename_i n₁
      cases ih_e₂ with
      | inl e₂_const =>
        cases e₂_const
        rename_i n₂
        apply HasDecomposition.decomposition (Expr.letIn name (Expr.const n₁) (Expr.const n₂))
          .hole (by simp)
        constructor
      | inr e₂_dec =>
        let ⟨e', ctx, e_eq, e'_redex⟩ := e₂_dec
        apply HasDecomposition.decomposition e' (.letInBody name n₁ ctx) (by simp [e_eq])
        assumption
    | inr e₁_dec =>
      let ⟨e', ctx, e_eq, e'_redex⟩ := e₁_dec
      apply HasDecomposition.decomposition e' (.letInExpr name ctx e₂) (by simp [e_eq])
      assumption
  · intro f es ih_es
    apply Or.intro_right
    apply HasDecomposition.decomposition (Expr.funCall f es) .hole (by simp)
    constructor

lemma redex_progress : ∀ {defs Γ e ty}, TypeJdg Γ e ty → IsRedex e →
  CtxRespectsEnv V Γ →  CtxRespectsDefs defs Γ →
  ∃ e', HeadSmallStep defs V e e' := by
  intro defs Γ e ty e_jdg e_redex V_resp_Γ defs_resp_Γ
  -- cases e_redex with
  -- | var =>
  --   cases e_jdg
  --   rename_i x x_ty
  --   sorry
  --   -- let _ := V_resp_Γ x x_ty
  sorry

theorem progress {Γ : TypeContext} {ty : LLType} {defs : Definitions}
  : TypeJdg Γ e ty → CtxRespectsEnv V Γ → CtxRespectsDefs defs Γ →
    IsConst e ∨ ∃ e', SmallStep defs V e e' := by
  intro e_jdg V_ext_Γ

  sorry

-- TODO: Also interesting:
-- if TypeJdg Γ e ty, then eval e succeeds
