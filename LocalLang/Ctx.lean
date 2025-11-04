import LocalLang.AST

inductive Ctx : Type where
  | hole : Ctx
  | binOpLhs : Ctx → BinOp → Expr → Ctx
  | binOpRhs : ℕ → BinOp → Ctx → Ctx
  | letInExpr : String → Ctx → Expr → Ctx
  | letInBody : String → ℕ → Ctx → Ctx

abbrev Env := Std.HashMap String ℕ

@[reducible] def Ctx.fill (e : Expr) : Ctx → Expr
  | hole => e
  | binOpLhs ctx op e' => Expr.binOp op (ctx.fill e) e'
  | binOpRhs n op ctx => Expr.binOp op (.const n) (ctx.fill e)
  | letInExpr x ctx e' => .letIn x (ctx.fill e) e'
  | letInBody x n ctx => .letIn x (.const n) (ctx.fill e)

def Ctx.updateEnv (env : Env) : Ctx → Env
  | hole => env
  | binOpLhs ctx _ _ => ctx.updateEnv env
  | binOpRhs _ _ ctx => ctx.updateEnv env
  | letInExpr _ ctx _ => ctx.updateEnv env
  | letInBody x n ctx => ctx.updateEnv (env.insert x n)
