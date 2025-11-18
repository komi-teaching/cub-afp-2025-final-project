import LocalLang.AST
import LocalLang.Evaluator
import LocalLang.Semantics

-- lemma smallStep_preserves_eval

-- TODO: eval e = k iff e steps to k
lemma eval_eq_some_of_smallSteps {defs : Definitions} : SmallSteps defs V e (.const n) →
  e.eval V defs = some n := by
  intro steps
  -- induction e
  sorry

lemma smallSteps_of_eval_eq_some {defs : Definitions} : e.eval V defs = some n →
  SmallSteps defs V e (.const n) := sorry

theorem eval_correct {defs : Definitions} : e.eval V defs = some n ↔
  SmallSteps defs V e (.const n) := Iff.intro smallSteps_of_eval_eq_some eval_eq_some_of_smallSteps
