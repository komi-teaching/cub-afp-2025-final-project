import LocalLang.Semantics
import LocalLang.SemanticsLemmas
import LocalLang.Ctx
import Mathlib.Data.List.Sigma
import Std.Data.HashMap.Basic
import Std.Data.HashMap.Lemmas

instance : Add Expr where
  add := .binOp .add

instance : Coe String Expr where
  coe := .var

instance : OfNat Expr n where
  ofNat := .const n

abbrev f_body : Expr := (.funCall "g" [ "x" + 1 ]) + "x"
abbrev f : Func := {
  parameters := ["x"],
  body := f_body
}
abbrev g : Func := {
  parameters := ["x"],
  body := "x"
}

abbrev defs := Std.HashMap.ofList [("f", f), ("g", g)]

@[simp] lemma defs_f : defs["f"] = f := by
  apply (Std.HashMap.getElem_ofList_of_mem (k := "f")) <;> simp
@[simp] lemma defs_g : defs["g"] = g := by
  apply (Std.HashMap.getElem_ofList_of_mem (k := "g")) <;> simp

lemma f_steps
  : SmallSteps defs (Std.HashMap.ofList [("x", 0)])
      (Expr.funCall "g" ["x" + 1] + Expr.var "x") 1 := by
  let locals := Std.HashMap.ofList [("x", 0)]
  calc
    SmallSteps defs locals _ (1 + "x") := by
      apply (SmallSteps.with_ctx (.binOpLhs .hole .add "x") rfl rfl)
      simp only [Ctx.updateEnv]
      calc
        SmallStep defs locals _ (.letIn "x" ("x" + 1) "x") := by
          apply SmallStep.hole_step
          apply (HeadSmallStep.fun_step ?_ rfl) <;> try rw [defs_g]
          · simp
          · rfl
          · simp
        SmallSteps defs locals _ (.letIn "x" 1 "x") := by
          apply (SmallSteps.with_ctx (.letInExpr "x" .hole "x") rfl rfl)
          calc
            SmallStep defs locals _ ((0 : Expr) + 1) := by
              apply (SmallStep.ctx_step (.binOpLhs .hole .add 1) rfl rfl)
              constructor
              simp [locals]
            SmallStep defs locals _ _ := by
              apply SmallStep.hole_step
              constructor
              rfl
        SmallStep defs locals _ (.letIn "x" 1 1) := by
          apply (SmallStep.ctx_step (.letInBody "x" 1 .hole) rfl rfl)
          constructor
          simp
        SmallStep defs locals _ 1 := by
          apply SmallStep.hole_step
          constructor
    SmallStep defs locals _ ((1 : Expr) + 0) := by
      apply (SmallStep.ctx_step (.binOpRhs 1 .add .hole) rfl rfl)
      constructor
      simp [locals]
    SmallStep defs locals _ _ := by
      apply SmallStep.hole_step
      constructor
      rfl

example : SmallSteps defs ∅ (.funCall "f" [0]) 1 := by
  calc
    SmallStep defs ∅ _ (.letIn "x" 0 f_body) := by
      apply SmallStep.hole_step
      apply (HeadSmallStep.fun_step ?_ rfl) <;> try rw [defs_f]
      · simp
      · rfl
      · simp
    SmallSteps defs ∅ _ (.letIn "x" 0 1) := by
      apply (SmallSteps.with_ctx (.letInBody "x" 0 .hole) rfl rfl)
      exact f_steps
    SmallStep defs ∅ _ _ := by
      apply SmallStep.hole_step
      constructor
