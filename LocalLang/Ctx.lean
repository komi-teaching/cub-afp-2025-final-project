import LocalLang.AST

inductive Ctx : Type where
  | hole : Ctx
  | binOpLhs : Ctx → BinOp → Expr → Ctx
  | binOpRhs : Value → BinOp → Ctx → Ctx
  | letInExpr : String → Ctx → Expr → Ctx
  | letInBody : String → Value → Ctx → Ctx
  | funCallBody : Ctx → List Expr → Ctx

@[reducible] def Ctx.fill (e : Expr) : Ctx → Expr
  | hole => e
  | binOpLhs ctx op e' => Expr.binOp op (ctx.fill e) e'
  | binOpRhs v op ctx => Expr.binOp op (.value v) (ctx.fill e)
  | letInExpr x ctx e' => .letIn x (ctx.fill e) e'
  | letInBody x v ctx => .letIn x (.value v) (ctx.fill e)
  | funCallBody ctx es => .funCall (ctx.fill e) es

@[reducible] def Ctx.updateEnv (env : Env) : Ctx → Env
  | hole => env
  | binOpLhs ctx _ _ => ctx.updateEnv env
  | binOpRhs _ _ ctx => ctx.updateEnv env
  | letInExpr _ ctx _ => ctx.updateEnv env
  | letInBody x v ctx => ctx.updateEnv (env.insert x v)
  | funCallBody ctx _ => ctx.updateEnv env

@[reducible] def Ctx.fillWithCtx (ctx : Ctx) (innerCtx : Ctx) : Ctx := match ctx with
  | .hole => innerCtx
  | .binOpLhs ctx₀ op e => .binOpLhs (Ctx.fillWithCtx ctx₀ innerCtx) op e
  | .binOpRhs n op ctx₀ => .binOpRhs n op (Ctx.fillWithCtx ctx₀ innerCtx)
  | .letInExpr x ctx₀ e => .letInExpr x (Ctx.fillWithCtx ctx₀ innerCtx) e
  | .letInBody x n ctx₀ => .letInBody x n (Ctx.fillWithCtx ctx₀ innerCtx)
  | .funCallBody ctx₀ es => .funCallBody (Ctx.fillWithCtx ctx₀ innerCtx) es
