import LocalLang.AST
import LocalLang.Evaluator
import LocalLang.Semantics

example {defs : Definitions} : V[x]? = some n → Expr.eval V defs (.var x) = some n := by
  intro h_in
  -- unfold Expr.eval     fails
  sorry

lemma headSmallStep_preserves_eval {defs : Definitions} : e₁.eval V defs = some n →
  HeadSmallStep defs V e₁ e₂ → e₂.eval V defs = some n := by
  intro e₁_eval_eq hstep
  cases hstep with
  | var_step h_in => sorry
  | bin_op_step => sorry
  | let_in_const_step => sorry
  | fun_step => sorry

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
