import LocalLang.Semantics
import LocalLang.SemanticsLemmas
import LocalLang.SemanticsTactics
import LocalLang.Ctx
import Mathlib.Data.List.Sigma
import Std.Data.HashMap.Basic
import Std.Data.HashMap.Lemmas

instance : Add Expr where
  add := .binOp .add

instance : Mul Expr where
  mul := .binOp .mul

instance : Coe String Expr where
  coe := .var

instance : OfNat Expr n where
  ofNat := .value (.nat n)

abbrev f_body : Expr := (.funCall "g" [ "x" + 1 ]) + "x"
abbrev f : Value := .closure ["x"] f_body
abbrev g : Value := .closure ["x"] "x"

abbrev defs := Std.HashMap.ofList [("f", f), ("g", g)]

--@[simp] lemma defs_f : defs["f"] = f := by
--  apply (Std.HashMap.getElem_ofList_of_mem (k := "f")) <;> simp
--@[simp] lemma defs_g : defs["g"] = g := by
--  apply (Std.HashMap.getElem_ofList_of_mem (k := "g")) <;> simp


example : SmallSteps defs (.funCall "f" [0]) 1 := by
  calc
    SmallStep defs _ (.funCall (.value (.closure ["x"] ((.funCall "g" [ "x" + 1 ]) + "x"))) [0]) := by
      step_auto_context
      solve_head
      apply (Std.HashMap.getElem_ofList_of_mem (k := "f")) <;> simp
    SmallStep defs _ (.letIn "x" 0 ((.funCall "g" [ "x" + 1 ]) + "x")) := by
      step_auto_context
      solve_head
    SmallStep defs _ (.letIn "x" 0 ((.funCall (.value (.closure ["x"] "x")) [ "x" + 1 ]) + "x")) := by
      step_auto_context
      solve_head
      apply (Std.HashMap.getElem_ofList_of_mem (k := "g")) <;> simp
    SmallStep defs _ (.letIn "x" 0 ((.letIn "x" ("x" + 1) "x") + "x")) := by
      step_auto_context
      solve_head
    SmallStep defs _ (.letIn "x" 0 ((.letIn "x" (0 + 1) "x") + "x")) := by
      step_auto_context
      solve_head
    SmallStep defs _ (.letIn "x" 0 ((.letIn "x" 1 "x") + "x")) := by
      step_auto_context
      solve_head
    SmallStep defs _ (.letIn "x" 0 ((.letIn "x" 1 1) + "x")) := by
      step_auto_context
      solve_head
    SmallStep defs _ (.letIn "x" 0 (1 + "x")) := by
      step_auto_context
      solve_head
    SmallStep defs _ (.letIn "x" 0 (1 + 0)) := by
      step_auto_context
      solve_head
    SmallStep defs _ (.letIn "x" 0 1) := by
      step_auto_context
      solve_head
    SmallStep defs _ 1 := by
      step_auto_context
      solve_head

example : SmallSteps (Std.HashMap.ofList [("x", 1)]) (.letIn "x" ("x" + 1) "x") 2 := by
  calc
    SmallStep (Std.HashMap.ofList [("x", 1)]) _ (.letIn "x" (1 + 1) "x") := by
      step_auto_context
      solve_head
      rfl
    SmallStep (Std.HashMap.ofList [("x", 1)]) _ (.letIn "x" 2 "x") := by
      step_auto_context
      solve_head
    SmallStep (Std.HashMap.ofList [("x", 1)]) _ (.letIn "x" 2 2) := by
      step_auto_context
      solve_head
    SmallStep (Std.HashMap.ofList [("x", 1)]) _ 2 := by
      step_auto_context
      solve_head

example : SmallSteps defs (.funCall "g" [1]) 1 := by
  calc
    SmallStep defs _ (.funCall (.value (.closure ["x"] "x")) [1]) := by
      step_auto_context
      solve_head
      apply (Std.HashMap.getElem_ofList_of_mem (k := "g")) <;> simp
    SmallStep defs _ (.letIn "x" 1 "x") := by
      step_auto_context
      solve_head
    SmallStep defs _ (.letIn "x" 1 1) := by
      step_auto_context
      solve_head
    SmallStep defs _ 1 := by
      step_auto_context
      solve_head

example : SmallSteps ∅ (1 + (1 + 1)) 3 := by
  calc
    SmallStep ∅ _ (1 + 2) := by
      step_auto_context
      solve_head
    SmallStep ∅ _ _ := by
      step_auto_context
      solve_head

example : SmallSteps ∅ (2 * (1 + 1)) 4 := by
  calc
    SmallStep ∅ _ (2 * 2) := by
      step_auto_context
      solve_head
    SmallStep ∅ _ _ := by
      step_auto_context
      solve_head

example : SmallSteps ∅ (.letIn "x" 1 "x") 1 := by
  calc
    SmallStep ∅ _ (.letIn "x" 1 1) := by
      step_auto_context
      solve_head
    SmallStep ∅ _ 1 := by
      step_auto_context
      solve_head

example : SmallSteps ∅ (.letIn "x" (2 + 2) ("x" * "x")) 16 := by
  calc
    SmallStep ∅ _ (.letIn "x" 4 ("x" * "x")) := by
      step_auto_context
      solve_head
    SmallStep ∅ _ (.letIn "x" 4 (4 * "x")) := by
      step_auto_context
      solve_head
    SmallStep ∅ _ (.letIn "x" 4 (4 * 4)) := by
      step_auto_context
      solve_head
    SmallStep ∅ _ (.letIn "x" 4 16) := by
      step_auto_context
      solve_head
    SmallStep ∅ _ 16 := by
      step_auto_context
      solve_head
