import LocalLang.Semantics
import Mathlib.Data.List.Sigma

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
  ["x"],
  f_body
⟩
def g : Function := ⟨
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

def defs_list := [("f", f), ("g", g)]
def defs := Std.HashMap.ofList defs_list

def f_at_defs : defs["f"]? = some f := by
  simp [defs]
  exact Std.HashMap.getElem?_ofList_of_mem (by rfl : "f" == "f") (by simp [defs_list])
          (by simp [defs_list])
def g_at_defs : defs["g"]? = some g := by
  simp [defs]
  exact Std.HashMap.getElem?_ofList_of_mem (by rfl : "g" == "g") (by simp [defs_list])
          (by simp [defs_list])

def step₁ : SmallStep defs ∅ e₁ e₂ := by
  let almost := @SmallStep.funStep defs "f" ∅ ["x"] f_body [.const 0]
    (by apply Std.HashMap.mem_ofList.mpr; simp [defs_list])
    (by simp)
  simp [letin_chain] at almost
  rw [Std.HashMap.getElem_eq_get_getElem?] at almost
  simp [f_at_defs, f] at almost
  assumption
def step₂ : SmallStep defs ∅ e₂ e₃ := by
  let a  :=
    @SmallStep.funStep defs "g" (.ofList [("x", 0)]) ["x"] g.body
      [.binOp .add (.var "x") (.const 1)] (by apply Std.HashMap.mem_ofList.mpr; simp [defs_list])
      (by simp)
  simp [letin_chain] at a
  rw [Std.HashMap.getElem_eq_get_getElem?] at a
  simp [g_at_defs, g] at a
  let b : SmallStep defs (.ofList [("x", 0)]) f_body f_body₂ :=
    .ctxStep (.binOpLhs .hole .add (.var "x")) (.ofList [("x", 0)]) a
  let c := SmallStep.ctxStep (.letInBody "x" 0 .hole) ∅ b
  rw [f_body, f_body₂] at c
  simp [Ctx.fill] at c
  rw [← f_body, ← f_body₂] at c
  rw [← e₂, ← e₃] at c
  assumption
def step₃ : SmallStep defs ∅ e₃ e₄ := by
  let a : SmallStep defs (.ofList [("x", 0)]) f_body₂ f_body₃ :=
    .ctxStep (.binOpLhs
      (.letInExpr "x" (.binOpLhs .hole .add (.const 1)) (.var "x"))
      .add
      (.var "x")
    ) (.ofList [("x", 0)]) (.varStep (by simp [Ctx.updateEnv]))
  let c := SmallStep.ctxStep (.letInBody "x" 0 .hole) ∅ a
  rw [f_body₂, f_body₃] at c
  simp [Ctx.fill] at c
  rw [← f_body₂, ← f_body₃] at c
  rw [← e₃, ← e₄] at c
  assumption
def step₄ : SmallStep defs ∅ e₄ e₅ := by
  let a : SmallStep defs (.ofList [("x", 0)]) f_body₃ f_body₄ :=
    .ctxStep (.binOpLhs
      (.letInExpr "x" .hole (.var "x"))
      .add
      (.var "x")
    ) (.ofList [("x", 0)]) .binOpStep
  let c := SmallStep.ctxStep (.letInBody "x" 0 .hole) ∅ a
  rw [f_body₃, f_body₄] at c
  simp [Ctx.fill] at c
  rw [← f_body₃, ← f_body₄] at c
  rw [← e₄, ← e₅] at c
  assumption
def step₅ : SmallStep defs ∅ e₅ e₆ := by
  let a : SmallStep defs (.ofList [("x", 0)])
    (.letIn "x" (.const 1) (.var "x"))
    (.letIn "x" (.const 1) (.const 1)) :=
    .ctxStep (.letInBody "x" 1 .hole) (.ofList [("x", 0)]) (.varStep (by simp [Ctx.updateEnv]))
  let b := SmallStep.ctxStep (.binOpLhs .hole .add (.var "x")) (.ofList [("x", 0)]) a
  let c := SmallStep.ctxStep (.letInBody "x" 0 .hole) ∅ b
  simp [Ctx.fill] at c
  rw [← f_body₄, ← f_body₅] at c
  rw [← e₅, ← e₆] at c
  assumption
def step₆ : SmallStep defs ∅ e₆ e₇ :=
  .ctxStep (.letInBody "x" 0 (.binOpLhs .hole .add (.var "x"))) ∅ .letinConstStep
def step₇ : SmallStep defs ∅ e₇ e₈ :=
  .ctxStep (.letInBody "x" 0 (.binOpRhs 1 .add .hole)) ∅ (.varStep (by simp [Ctx.updateEnv]))
def step₈ : SmallStep defs ∅ e₈ e₉ :=
  .ctxStep (.letInBody "x" 0 .hole) ∅ .binOpStep
def step₉ : SmallStep defs ∅ e₉ (.const 1) :=
  .letinConstStep

infixr:100 " ~> " => SmallSteps defs ∅

def steps : e₁ ~> (.const 1) := by
  calc
    e₁ ~> e₂ := SmallSteps.single step₁
    e₂ ~> e₃ := SmallSteps.single step₂
    e₃ ~> e₄ := SmallSteps.single step₃
    e₄ ~> e₅ := SmallSteps.single step₄
    e₅ ~> e₆ := SmallSteps.single step₅
    e₆ ~> e₇ := SmallSteps.single step₆
    e₇ ~> e₈ := SmallSteps.single step₇
    e₈ ~> e₉ := SmallSteps.single step₈
    e₉ ~> (.const 1) := SmallSteps.single step₉
