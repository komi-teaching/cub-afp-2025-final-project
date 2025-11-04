import LocalLang.AST

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
