import LocalLang.AST
import LocalLang.Semantics
import LocalLang.Types
import LocalLang.Typing

def EnvRespectsCtx (Γ : TypeContext) (V : Env) : Prop :=
  sorry

def CtxRespectsEnv (V : Env) (Γ : TypeContext) : Prop :=
  sorry

inductive IsFuncType : LLType → Prop where
  | func {param_tys ret_ty} : IsFuncType (.func param_tys ret_ty)

-- def CtxRespectsDefs (defs : Definitions) (Γ : TypeContext) : Prop :=
--   sorry

-- TODO: prove
-- TODO: V and Γ should be related
theorem preservation (Γ : TypeContext) (e e' : Expr) (ty : LLType)
    (h_env_respects : EnvRespectsCtx Γ V)
  : Expr.TypeJdg Γ e ty → HeadSmallStep V e e' → Expr.TypeJdg Γ e' ty := by
  sorry

-- Progress: if TypeJdg Γ e ty, then e can take a step.
-- TODO: formalize

def Expr.simple_rec.{l} {motive : Expr → Sort l}
     (value_case : ∀ v, motive (.value v))
     (const_case : ∀ n, motive (.const n))
     (var_case : ∀ x, motive (.var x))
     (bin_op_case : ∀ op lhs rhs, motive lhs → motive rhs → motive (.binOp op lhs rhs))
     (let_in_case : ∀ name e₁ e₂, motive e₁ → motive e₂ → motive (.letIn name e₁ e₂))
     (fun_case : ∀ f es, (∀ e', e' ∈ es → motive e') → motive (.funCall f es))
    : (e : Expr) → motive e := go
where go
  | .value v => value_case v
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
  sorry

lemma redex_progress : ∀ {Γ e ty}, Expr.TypeJdg Γ e ty → IsRedex e →
  CtxRespectsEnv V Γ → ∃ e', HeadSmallStep V e e' := by
  sorry

theorem progress {Γ : TypeContext} {ty : LLType}
  : Expr.TypeJdg Γ e ty → CtxRespectsEnv V Γ →
    IsConst e ∨ ∃ e', SmallStep V e e' := by
  intro e_jdg V_ext_Γ
  sorry

-- TODO: Also interesting:
-- if TypeJdg Γ e ty, then eval e succeeds
