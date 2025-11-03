import LocalLang.AST

inductive Ctx : Type where
  | hole : Ctx
  | bin_op_lhs : Ctx → BinOp → Expr → Ctx
  | bin_op_rhs : ℕ → BinOp → Ctx → Ctx
  | fun_call : String → List ℕ → Ctx → List Expr → Ctx

def Ctx.fill (e : Expr) : Ctx → Expr
  | hole => e
  | bin_op_lhs ctx op e' => Expr.binOp op (ctx.fill e) e'
  | bin_op_rhs n op ctx => Expr.binOp op (.const n) (ctx.fill e)
  | fun_call f es_left ctx es_right =>
      Expr.funCall f ((.const ·) <$> es_left ++ [ctx.fill e] ++ es_right)

abbrev VarContext := Std.HashMap String ℕ

-- TODO: define
inductive SmallStep (defs : Definitions) : (VarContext × Expr) → (VarContext × Expr) → Prop where
  | var_step : V[x]? = some n →
      SmallStep defs (V, (.var x)) (V, .const n)
  | bin_op_step {op : BinOp} :
      SmallStep defs (V, .binOp op (.const e₁) (.const e₂)) (V, .const <| op.eval e₁ e₂)
  | ctx_step (ctx : Ctx) : SmallStep defs (V, e₁) (V, e₂) →
      SmallStep defs (V, ctx.fill e₁) (V, ctx.fill e₂)
  | fun_step {es : List ℕ} {func : Function} (Hf : defs.find? (·.name = f) = some func)
      (Hpn : func.parameters.length = es.length):
      SmallStep defs
        (V, .funCall f <| (.const ·) <$> es)
        (.ofList <| V.toList ++ func.parameters.zip es, func.body)

-- TODO: define
inductive SmallSteps (defs : Definitions) : (VarContext × Expr) → (VarContext × Expr) → Prop where
  | trivial : SmallSteps defs (V, e) (V, e)
  | cons : SmallStep defs (V₁, e₁) (V₂, e₂) → SmallSteps defs (V₂, e₂) (V₃, e₃) →
      SmallSteps defs (V₁, e₁) (V₃, e₃)

-- TODO: prove
theorem smallSteps_diamond {defs : Definitions} {e₁ e₂ e₃ : Expr}
  (HA : SmallSteps defs (V₁, e₁) (V₂, e₂)) (HB : SmallSteps defs (V₁, e₁) (V₃, e₃))
  :  ∃ V₄ e₄, SmallSteps defs (V₂, e₂) (V₄, e₄) ∧ SmallSteps defs (V₃, e₃) (V₄, e₄) := sorry
