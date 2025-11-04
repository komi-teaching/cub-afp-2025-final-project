import LocalLang.AST
import LocalLang.Evaluator

inductive Ctx : Type where
  | hole : Ctx
  | bin_op_lhs : Ctx → BinOp → Expr → Ctx
  | bin_op_rhs : ℕ → BinOp → Ctx → Ctx
  | letin : String → Ctx → Expr → Ctx

def Ctx.fill (e : Expr) : Ctx → Expr
  | hole => e
  | bin_op_lhs ctx op e' => Expr.binOp op (ctx.fill e) e'
  | bin_op_rhs n op ctx => Expr.binOp op (.const n) (ctx.fill e)
  | letin x ctx e' => .letIn x (ctx.fill e) e'

abbrev Env := Std.HashMap String ℕ

-- .funCall f
def letin_chain (vars : List (String × Expr)) (e : Expr) : Expr := match vars with
  | .nil => e
  | .cons (name, expr) vs => .letIn name expr <| letin_chain vs e

-- TODO: define
inductive SmallStep (defs : Definitions) : Env → Expr → Expr → Prop where
  | var_step : V[x]? = some n →
      SmallStep defs V (.var x) (.const n)
  | bin_op_step {op : BinOp} :
      SmallStep defs V (.binOp op (.const e₁) (.const e₂)) (.const <| op.eval e₁ e₂)
  | ctx_step (ctx : Ctx) : SmallStep defs V e₁ e₂ →
      SmallStep defs V (ctx.fill e₁) (ctx.fill e₂)
  | letin_cong {name : String} {val : ℕ} : SmallStep defs (V.insert name val) e₁ e₂ →
      SmallStep defs V (.letIn name (.const val) e₁) (.letIn name (.const val) e₂)
  | letin_const_step {name : String} {val n : ℕ} :
      SmallStep defs V (.letIn name (.const val) (.const n)) (.const n)
  | fun_step {ps : List String} {body : Expr} {es : List Expr}
      (Hf : ⟨f, ps, body⟩ ∈ defs) (Hpn : ps.length = es.length) :
      SmallStep defs V (.funCall f es) (letin_chain (ps.zip es) body)

-- TODO: define
inductive SmallSteps (defs : Definitions) : Env → Expr → Expr → Prop where
  | trivial : SmallSteps defs V e e
  | cons : SmallStep defs V e₁ e₂ → SmallSteps defs V e₂ e₃ →
      SmallSteps defs V e₁ e₃

-- TODO: prove
theorem smallSteps_diamond {defs : Definitions} {e₁ e₂ e₃ : Expr}
  (HA : SmallSteps defs V e₁ e₂) (HB : SmallSteps defs V e₁ e₃)
  :  ∃ e₄, SmallSteps defs V e₂ e₄ ∧ SmallSteps defs V e₃ e₄ := sorry
