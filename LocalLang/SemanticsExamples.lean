import LocalLang.Semantics

def f_body : Expr := .binOp .add
  (
    .funCall "g" [
      .binOp .add (.var "x") (.const 1)
    ]
  )
  (
    .var "x"
  )
def f : Function := ⟨
  "f",
  ["x"],
  f_body
⟩
def g : Function := ⟨
  "g",
  ["x"],
  .var "x"
⟩

def f_body₂ : Expr := .binOp .add
  (.letIn "x" (.binOp .add (.var "x") (.const 1)) (.var "x"))
  (.var "x")
def f_body₃ : Expr := .binOp .add
  (.letIn "x" (.binOp .add (.const 0) (.const 1)) (.var "x"))
  (.var "x")
def f_body₄ : Expr := .binOp .add
  (.letIn "x" (.const 1) (.var "x"))
  (.var "x")
def f_body₅ : Expr := .binOp .add
  (.letIn "x" (.const 1) (.const 1))
  (.var "x")
def f_body₆ : Expr := .binOp .add (.const 1) (.var "x")
def f_body₇ : Expr := .binOp .add (.const 1) (.const 0)
def f_body₈ : Expr := .const 1
def e₁ : Expr := .funCall "f" [.const 0]
def e₂ : Expr := .letIn "x" (.const 0) f_body
def e₃ : Expr := .letIn "x" (.const 0) f_body₂
def e₄ : Expr := .letIn "x" (.const 0) f_body₃
def e₅ : Expr := .letIn "x" (.const 0) f_body₄
def e₆ : Expr := .letIn "x" (.const 0) f_body₅
def e₇ : Expr := .letIn "x" (.const 0) f_body₆
def e₈ : Expr := .letIn "x" (.const 0) f_body₇
def e₉ : Expr := .letIn "x" (.const 0) f_body₈
def e₁₀ : Expr := .const 1
def step₁ : SmallStep [f, g] ∅ e₁ e₂ := by
  let almost := @SmallStep.fun_step [f, g] ∅ "f" ["x"] f_body [.const 0] (by simp [f]) (by simp)
  simp [f, letin_chain] at almost
  rw [← f, ← e₁, ← e₂] at almost
  assumption
def step₂ : SmallStep [f, g] ∅ e₂ e₃ := by
  let a : SmallStep [f, g] (.ofList [("x", 0)])
    (.funCall "g" [.binOp .add (.var "x") (.const 1)])
    (.letIn "x" (.binOp .add (.var "x") (.const 1)) (.var "x")) :=
    @SmallStep.fun_step [f, g] (.ofList [("x", 0)]) "g" ["x"] g.body
      [.binOp .add (.var "x") (.const 1)] (by simp [f, g]) (by simp)
  let b : SmallStep [f, g] (.ofList [("x", 0)]) f_body f_body₂ :=
    .ctx_step (.bin_op_lhs .hole .add (.var "x")) a
  exact .letin_cong b
def step₃ : SmallStep [f, g] ∅ e₃ e₄ := by
  let a : SmallStep [f, g] (.ofList [("x", 0)]) f_body₂ f_body₃ :=
    .ctx_step (.bin_op_lhs
      (.letin "x" (.bin_op_lhs .hole .add (.const 1)) (.var "x"))
      .add
      (.var "x")
    ) (.var_step (by simp))
  exact .letin_cong a
def step₄ : SmallStep [f, g] ∅ e₄ e₅ := by
  let a : SmallStep [f, g] (.ofList [("x", 0)]) f_body₃ f_body₄ :=
    .ctx_step (.bin_op_lhs
      (.letin "x" .hole (.var "x"))
      .add
      (.var "x")
    ) .bin_op_step
  exact .letin_cong a
def step₅ : SmallStep [f, g] ∅ e₅ e₆ := by
  let a : SmallStep [f, g] (.ofList [("x", 0)])
    (.letIn "x" (.const 1) (.var "x"))
    (.letIn "x" (.const 1) (.const 1)) :=
    .letin_cong (.var_step (by simp))
  let b := SmallStep.ctx_step (.bin_op_lhs .hole .add (.var "x")) a
  exact .letin_cong b
def step₆ : SmallStep [f, g] ∅ e₆ e₇ :=
  .letin_cong <| SmallStep.ctx_step (.bin_op_lhs .hole .add (.var "x")) .letin_const_step
def step₇ : SmallStep [f, g] ∅ e₇ e₈ :=
  .letin_cong <| .ctx_step (.bin_op_rhs 1 .add .hole) (.var_step (by simp))
def step₈ : SmallStep [f, g] ∅ e₈ e₉ :=
  .letin_cong <| .bin_op_step
def step₉ : SmallStep [f, g] ∅ e₉ e₁₀ :=
  .letin_const_step

-- def steps : SmallSteps [f, g] ∅ e₁ (.const 1) :=
--   [step₁, step₂, step₃, step₄, step₅, step₆, step₇, step₈, step₉].foldr
--   (fun st sts => Relation.ReflTransGen.tail sts st) Relation.ReflTransGen.refl
def steps : SmallSteps [f, g] ∅ e₁ (.const 1) := .cons step₁ <| .cons step₂ <| .cons step₃ <|
  .cons step₄ <| .cons step₅ <| .cons step₆ <| .cons step₇ <| .cons step₈ <| .cons step₉ <| .trivial
