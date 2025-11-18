import LocalLang.Semantics
import LocalLang.SemanticsLemmas

lemma headSmallStep_deterministic {defs : Definitions}
    (hst₁ : HeadSmallStep defs V e e₁) (hst₂ : HeadSmallStep defs V e e₂)
    : e₁ = e₂ := by
  cases hst₁ <;> cases hst₂ <;> congr
  · rename_i n₁ h_n₁ n₂ h_n₂
    suffices some n₁ = some n₂ by cases this; rfl
    rw [← h_n₁, ← h_n₂]
  all_goals subst_eqs; rfl

theorem smallStep_deterministic {defs : Definitions}
    (st₁ : SmallStep defs V e e₁) (st₂ : SmallStep defs V e e₂) : e₁ = e₂ := by
  rcases st₁ with ⟨ctx₁, h₁, rfl, hst₁⟩
  rcases st₂ with ⟨ctx₂, h₂, rfl, hst₂⟩
  rename_i e₁ e₁' e₂ e₂'
  have : ctx₁ = ctx₂ := by
    apply fill_redex_injective_in_ctx
    · exact redex_of_headSmallStep hst₁
    · exact redex_of_headSmallStep hst₂
    rw [← h₁, h₂]
  subst_eqs
  cases fill_injective h₂
  congr
  apply headSmallStep_deterministic <;> trivial

theorem smallSteps_diamond {defs : Definitions} {e e₁ e₂ : Expr}
    (st₁ : SmallSteps defs V e e₁) (st₂ : SmallSteps defs V e e₂)
    : Relation.Join (SmallSteps defs V) e₁ e₂ := by
  apply Relation.church_rosser ?_ st₁ st₂
  intro a b c st_a st_b
  use c
  cases smallStep_deterministic st_a st_b
  repeat constructor
