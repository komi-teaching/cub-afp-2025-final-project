import LocalLang.Semantics
import Mathlib.Data.List.Sigma
import Std.Data.ExtHashMap.Basic
import Std.Data.ExtHashMap.Lemmas

abbrev f_body : Expr := .binOp .add
  (
    .funCall "g" [
      .binOp .add (.var "x") (.const 1)
    ]
  )
  (
    .var "x"
  )
abbrev f : Function := ⟨
  ["x"],
  f_body
⟩
abbrev g : Function := ⟨
  ["x"],
  .var "x"
⟩

abbrev f_body₂ : Expr := .binOp .add
  (.letIn "x" (.binOp .add (.var "x") (.const 1)) (.var "x"))
  (.var "x")
abbrev f_body₃ : Expr := .binOp .add
  (.letIn "x" (.binOp .add (.const 0) (.const 1)) (.var "x"))
  (.var "x")
abbrev f_body₄ : Expr := .binOp .add
  (.letIn "x" (.const 1) (.var "x"))
  (.var "x")
abbrev f_body₅ : Expr := .binOp .add
  (.letIn "x" (.const 1) (.const 1))
  (.var "x")
abbrev f_body₆ : Expr := .binOp .add (.const 1) (.var "x")
abbrev f_body₇ : Expr := .binOp .add (.const 1) (.const 0)
abbrev f_body₈ : Expr := .const 1

def defs_list := [("f", f), ("g", g)]
def defs := Std.HashMap.ofList defs_list

lemma f_at_defs : defs["f"]? = some f := by
  simp [defs]
  exact Std.HashMap.getElem?_ofList_of_mem (by rfl : "f" == "f") (by simp [defs_list])
          (by simp [defs_list])
lemma g_at_defs : defs["g"]? = some g := by
  simp [defs]
  exact Std.HashMap.getElem?_ofList_of_mem (by rfl : "g" == "g") (by simp [defs_list])
          (by simp [defs_list])

infixr:100 " ~> " => SmallStep defs ∅
infixr:100 " ~~> " => SmallSteps defs ∅

instance {defs : Definitions} :
  Trans (SmallStep defs V) (SmallStep defs V) (SmallSteps defs V) where
    trans st₁ st₂ := Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single st₁) (Relation.ReflTransGen.single st₂)

lemma step_in_context_implies_step_in_expr {e₁ e₂ e₁' e₂' : Expr} {V V' : Env}
  (st : SmallStep defs V' e₁ e₂) (ctx : Ctx) (HEnv : V' = ctx.updateEnv V)
  (He₁ : e₁' = ctx.fill e₁) (He₂ : e₂' = ctx.fill e₂) : SmallStep defs V e₁' e₂' := by
  rw [HEnv] at st
  let result := SmallStep.ctx_step ctx V st
  rw [← He₁, ← He₂] at result
  assumption

lemma step_in_body_implies_step_in_expr {body body' : Expr}
  (st : SmallStep defs (.ofList [("x", 0)]) body body') :
  .letIn "x" (.const 0) body ~> .letIn "x" (.const 0) body' := step_in_context_implies_step_in_expr
    st (.letInBody "x" 0 .hole) (by simp [Ctx.updateEnv]) (by simp [Ctx.fill]) (by simp [Ctx.fill])

example : .funCall "f" [.const 0] ~~> (.const 1) := by
  calc
    _ ~> .letIn "x" (.const 0) f_body := by
      let result := @SmallStep.fun_step defs "f" ∅ ["x"] f_body [.const 0]
        (by apply Std.HashMap.mem_ofList.mpr; simp [defs_list])
        (by simp)
      simp [letin_chain] at result
      rw [Std.HashMap.getElem_eq_get_getElem?] at result
      simp [f_at_defs] at result
      assumption
    _ ~> .letIn "x" (.const 0) f_body₂ := by
      let body_step :=
        @SmallStep.fun_step defs "g" (.ofList [("x", 0)]) ["x"] g.body
          [.binOp .add (.var "x") (.const 1)]
          (by apply Std.HashMap.mem_ofList.mpr; simp [defs_list])
          (by simp)
      simp [letin_chain] at body_step
      rw [Std.HashMap.getElem_eq_get_getElem?] at body_step
      simp [g_at_defs] at body_step
      apply step_in_body_implies_step_in_expr
      exact .ctx_step (.binOpLhs .hole .add (.var "x")) (.ofList [("x", 0)]) body_step
    _ ~> .letIn "x" (.const 0) f_body₃ := step_in_body_implies_step_in_expr <|
      .ctx_step (.binOpLhs
          (.letInExpr "x" (.binOpLhs .hole .add (.const 1)) (.var "x"))
          .add
          (.var "x")
        ) (.ofList [("x", 0)]) (.var_step (by simp [Ctx.updateEnv]))
    _ ~> .letIn "x" (.const 0) f_body₄ := step_in_body_implies_step_in_expr <|
        .ctx_step (.binOpLhs
          (.letInExpr "x" .hole (.var "x"))
          .add
          (.var "x")
        ) (.ofList [("x", 0)]) .bin_op_step
    _ ~> .letIn "x" (.const 0) f_body₅ := step_in_context_implies_step_in_expr
        (.var_step (by simp) :
          SmallStep defs ((Std.HashMap.insert ∅ "x" 0).insert "x" 1) (.var "x") (.const 1))
        (.letInBody "x" 0 (.binOpLhs (.letInBody "x" 1 .hole) .add (.var "x")))
        (by simp [Ctx.updateEnv]) (by simp [Ctx.fill]) (by simp [Ctx.fill])
    _ ~> .letIn "x" (.const 0) f_body₆ :=
      .ctx_step (.letInBody "x" 0 (.binOpLhs .hole .add (.var "x"))) ∅ .letin_const_step
    _ ~> .letIn "x" (.const 0) f_body₇ :=
      .ctx_step (.letInBody "x" 0 (.binOpRhs 1 .add .hole)) ∅ (.var_step (by simp [Ctx.updateEnv]))
    _ ~> .letIn "x" (.const 0) f_body₈ := .ctx_step (.letInBody "x" 0 .hole) ∅ .bin_op_step
    _ ~> (.const 1) := .letin_const_step
