import LocalLang.Semantics
import LocalLang.SemanticsLemmas

theorem smallStep_deterministic
  (h_a : SmallStep V e₁ e₂) (h_b : SmallStep V e₁ e₃) : e₂ = e₃ := sorry

theorem smallSteps_diamond {e₁ e₂ e₃ : Expr}
  (h_a : SmallSteps V e₁ e₂) (h_b : SmallSteps V e₁ e₃)
  :  ∃ e₄, SmallSteps V e₂ e₄ ∧ SmallSteps V e₃ e₄ := by
  suffices Relation.Join (SmallSteps V) e₂ e₃ by
    let ⟨e₄, _⟩ := this
    use e₄
  apply Relation.church_rosser ?_ h_a h_b
  intro a b c st_a st_b
  use c
  let b_eq_c := smallStep_deterministic st_a st_b
  rw [b_eq_c]
  constructor
  · exact Relation.ReflGen.refl
  · exact Relation.ReflTransGen.refl
