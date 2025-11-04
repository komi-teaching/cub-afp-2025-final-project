import LocalLang.AST

inductive Ctx : Type where
  | hole : Ctx
  | binOpLhs : Ctx → BinOp → Expr → Ctx
  | binOpRhs : ℕ → BinOp → Ctx → Ctx
  | letIn : String → Ctx → Expr → Ctx

def Ctx.fill (e : Expr) : Ctx → Expr
  | hole => e
  | binOpLhs ctx op e' => Expr.binOp op (ctx.fill e) e'
  | binOpRhs n op ctx => Expr.binOp op (.const n) (ctx.fill e)
  | letIn x ctx e' => .letIn x (ctx.fill e) e'
