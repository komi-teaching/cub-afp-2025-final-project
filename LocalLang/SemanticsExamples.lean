import LocalLang.Semantics
import LocalLang.SemanticsLemmas
import LocalLang.SemanticsTactics
import LocalLang.Ctx
import Mathlib.Data.List.Sigma
import Std.Data.HashMap.Basic
import Std.Data.HashMap.Lemmas

instance : Add Expr where
  add := .binOp .add

instance : Coe String Expr where
  coe := .var

instance : OfNat Expr n where
  ofNat := .value (.nat n)

abbrev f_body : Expr := (.funCall "g" [ "x" + 1 ]) + "x"
abbrev f : Value := .closure ["x"] f_body
abbrev g : Value := .closure ["x"] "x"

abbrev defs := Std.HashMap.ofList [("f", f), ("g", g)]

@[simp] lemma defs_f : defs["f"] = f := by
  apply (Std.HashMap.getElem_ofList_of_mem (k := "f")) <;> simp
@[simp] lemma defs_g : defs["g"] = g := by
  apply (Std.HashMap.getElem_ofList_of_mem (k := "g")) <;> simp

lemma f_steps
  : SmallSteps (defs.insert "x" 0)
      (Expr.funCall "g" ["x" + 1] + Expr.var "x") 1 := by
  let env := defs.insert "x" 0
  calc
    SmallSteps env _ (1 + "x") := by
      apply (SmallSteps.with_ctx (.binOpLhs .hole .add "x") rfl rfl)
      simp only [Ctx.updateEnv]
      calc
        SmallStep env _ (.funCall (.value (.closure ["x"] "x")) ["x" + 1]) := by
          step_auto_context
          apply HeadSmallStep.var_step
          simp [env, Std.HashMap.getElem_insert]
        SmallStep env _ (.letIn "x" ("x" + 1) "x") := by
          step_auto_context
          apply (HeadSmallStep.fun_step ?_ rfl)
          try rw [defs_g]
          simp
        SmallSteps env _ (.letIn "x" 1 "x") := by
          apply (SmallSteps.with_ctx (.letInExpr "x" .hole "x") rfl rfl)
          simp only [Ctx.updateEnv]
          calc
            SmallStep env _ (0 + 1) := by
              step_auto_context
              apply HeadSmallStep.var_step
              simp [Ctx.updateEnv, env]
              rfl
            SmallStep env _ _ := by
              step_auto_context
              apply HeadSmallStep.bin_op_step
              constructor
        SmallStep env _ (.letIn "x" 1 1) := by
          step_auto_context
        SmallStep env _ 1 := by
          step_auto_context
          constructor
    SmallStep env _ (1 + 0) := by
      step_auto_context
    SmallStep env _ _ := by
      step_auto_context
      constructor
      rfl

example : SmallSteps defs (.funCall "f" [0]) 1 := by
  calc
    SmallStep defs _ (.funCall (.value (.closure ["x"] f_body)) [0]) := by
      apply SmallStep.ctx_step (.funCallBody .hole [0]) (by simp) (by simp)
        (?_ : HeadSmallStep _ "f" (.value (.closure ["x"] f_body)))
      constructor
      simp
    SmallStep defs _ (.letIn "x" 0 f_body) := by
      apply SmallStep.hole_step
      apply (HeadSmallStep.fun_step ?_ rfl)
      try rw [defs_f]
      simp
    SmallSteps defs _ (.letIn "x" 0 1) := by
      apply (SmallSteps.with_ctx (.letInBody "x" 0 .hole) rfl rfl)
      exact f_steps
    SmallStep defs _ _ := by
      apply SmallStep.hole_step
      constructor
