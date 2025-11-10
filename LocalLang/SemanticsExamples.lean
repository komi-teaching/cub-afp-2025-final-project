import LocalLang.Semantics
import LocalLang.Ctx
import Mathlib.Data.List.Sigma
import Std.Data.HashMap.Basic

instance : Add Expr where
  add := .binOp .add

instance : Coe String Expr where
  coe := .var

instance : OfNat Expr n where
  ofNat := .const n

abbrev f_body : Expr := (.funCall "g" [ "x" + 1 ]) + "x"
abbrev f : Function := {
  parameters := ["x"],
  body := f_body
}
abbrev g : Function := {
  parameters := ["x"],
  body := "x"
}

abbrev defs := Std.HashMap.ofList [("f", f), ("g", g)]
abbrev varsf := Std.HashMap.ofList [("x", 0)]

/-
lemma f_at_defs : defs["f"]? = some f := by
  exact Std.HashMap.getElem?_ofList_of_mem (by rfl : "f" == "f") (by simp [defs_list])
          (by simp)
lemma g_at_defs : defs["g"]? = some g := by
  simp [defs]
  exact Std.HashMap.getElem?_ofList_of_mem (by rfl : "g" == "g") (by simp [defs_list])
          (by simp [defs_list])
-/

infixr:100 " ~> " => SmallStep defs _
infixr:100 " ~~> " => SmallSteps defs _

/-
lemma step_in_body_implies_step_in_expr {body body' : Expr}
  (st : SmallStep defs (.ofList [("x", 0)]) body body') :
  .letIn "x" (.const 0) body ~> .letIn "x" (.const 0) body' := step_in_context_implies_step_in_expr
    st (.letInBody "x" 0 .hole) (by simp [Ctx.updateEnv]) (by simp [Ctx.fill]) (by simp [Ctx.fill])
    -/

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


instance {defs : Definitions} :
  Trans (SmallStep defs V) (SmallStep defs V) (SmallSteps defs V) where
    trans st₁ st₂ := Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single st₁) (Relation.ReflTransGen.single st₂)

@[simp] lemma defs_f : defs["f"] = f := sorry
@[simp] lemma f_in_defs : "f" ∈ defs := sorry

example : SmallSteps defs ∅ (.funCall "f" [0]) 1 := by
  calc
    SmallStep defs ∅ _ (.letIn "x" 0 f_body) := by
      apply (SmallStep.ctx_step .hole rfl rfl)
      apply (HeadSmallStep.fun_step ?_ rfl) <;> try rw [defs_f]
      · simp [letin_chain]
      · rfl
      · simp




/-
    SmallStep defs ∅ _ (.letIn "x" (.const 0) f_body₂) := by
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

-/
