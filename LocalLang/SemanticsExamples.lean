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


example : SmallSteps defs (.funCall "f" [0]) 1 := by
  calc
    SmallStep defs _
        (.funCall (.value (.closure ["x"] ((.funCall "g" [ "x" + 1 ]) + "x"))) [0]) := by

      machine_step
    SmallStep defs _ (.letIn "x" 0 ((.funCall "g" [ "x" + 1 ]) + "x")) := by
      machine_step
    SmallStep defs _
        (.letIn "x" 0 ((.funCall (.value (.closure ["x"] "x")) [ "x" + 1 ]) + "x")) := by
      machine_step
    SmallStep defs _ (.letIn "x" 0 ((.letIn "x" ("x" + 1) "x") + "x")) := by
      machine_step
    SmallStep defs _ (.letIn "x" 0 ((.letIn "x" (0 + 1) "x") + "x")) := by
      machine_step
    SmallStep defs _ (.letIn "x" 0 ((.letIn "x" 1 "x") + "x")) := by
      machine_step
    SmallStep defs _ (.letIn "x" 0 ((.letIn "x" 1 1) + "x")) := by
      machine_step
    SmallStep defs _ (.letIn "x" 0 (1 + "x")) := by
      machine_step
    SmallStep defs _ (.letIn "x" 0 (1 + 0)) := by
      machine_step
    SmallStep defs _ (.letIn "x" 0 1) := by
      machine_step
    SmallStep defs _ 1 := by
      machine_step

example : SmallSteps (Std.HashMap.insert ∅ "f" (.closure ["x", "y"] ("x" + "y"))) (.funCall "f" [2, 3]) 5 := by
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  rfl

example : SmallSteps (Std.HashMap.insert (Std.HashMap.insert ∅ "f" (.closure ["x"] ((.funCall "g" [ "x" + 1 ]) + "x"))) "g" (.closure ["x"] "x")) (.funCall "f" [0]) 1 := by
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  rfl

example : SmallSteps (Std.HashMap.ofList [("x", 1)]) (.letIn "x" ("x" + 1) "x") 2 := by
  calc
    SmallStep (Std.HashMap.ofList [("x", 1)]) _ (.letIn "x" (1 + 1) "x") := by
      machine_step
    SmallStep (Std.HashMap.ofList [("x", 1)]) _ (.letIn "x" 2 "x") := by
      machine_step
    SmallStep (Std.HashMap.ofList [("x", 1)]) _ (.letIn "x" 2 2) := by
      machine_step
    SmallStep (Std.HashMap.ofList [("x", 1)]) _ 2 := by
      machine_step

example : SmallSteps (Std.HashMap.insert ∅ "x" 1) (.letIn "x" ("x" + 1) "x") 2 := by
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  rfl


example : SmallSteps defs (.funCall "g" [1]) 1 := by
  calc
    SmallStep defs _ (.funCall (.value (.closure ["x"] "x")) [1]) := by
      machine_step
    SmallStep defs _ (.letIn "x" 1 "x") := by
      machine_step
    SmallStep defs _ (.letIn "x" 1 1) := by
      machine_step
    SmallStep defs _ 1 := by
      machine_step

example : SmallSteps ∅ (1 + (1 + 1)) 3 := by
  calc
    SmallStep ∅ _ (1 + 2) := by
      machine_step
    SmallStep ∅ _ _ := by
      machine_step

example : SmallSteps ∅ (1 + (1 + 1)) 3 := by
  machine_solve

example : SmallSteps ∅ (2 * (1 + 1)) 4 := by
  machine_solve

/-
example : SmallSteps (Std.HashMap.ofList [("x", 1)]) "x" 1 := by
  calc
    SmallStep (Std.HashMap.ofList [("x", 1)]) _ 1 := by
      machine_step
    SmallSteps (Std.HashMap.ofList [("x", 1)]) 1 1 := by
      rfl
-/

example : SmallSteps ∅ (.letIn "x" 1 "x") 1 := by
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  rfl

example : SmallSteps ∅ (.letIn "x" (2 + 3) ("x" * "x")) 25 := by
  apply Relation.ReflTransGen.head (b := (.letIn "x" 5 ("x" * "x")))
  . machine_step
  rw[to_rw]
  apply Relation.ReflTransGen.head (b := (.letIn "x" 5 (5 * "x")))
  . machine_step
  rw[to_rw]
  apply Relation.ReflTransGen.head (b := (.letIn "x" 5 (5 * 5)))
  . machine_step
  rw[to_rw]
  apply Relation.ReflTransGen.head (b := (.letIn "x" 5 25))
  . machine_step
  rw[to_rw]
  apply Relation.ReflTransGen.head (b := 25)
  . machine_step
  rw[to_rw]

example : SmallSteps ∅ (.letIn "x" (2 + 3) ("x" * "x")) 25 := by
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  rfl

example : SmallSteps ∅ (.letIn "x" (2 + 3) ("x" * "x")) 25 := by
  repeat
    take_next_step
    . machine_step
    rw[to_rw]
  rfl

example : SmallSteps ∅ (.letIn "x" (2 + 3) ("x" * "x")) 25 := by
  machine_solve



example : SmallSteps ∅ (.letIn "x" 5 ("x" * 3)) 15 := by
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  rfl



example : SmallSteps (Std.HashMap.insert ∅ "x" 5) ("x" * 3) 15 := by
  take_next_step
  . machine_step
  rw[to_rw]
  take_next_step
  . machine_step
  rw[to_rw]
  rfl


example : SmallSteps ∅ (.letIn "x" (2 + 2) ("x" * "x")) 16 := by
  machine_solve
