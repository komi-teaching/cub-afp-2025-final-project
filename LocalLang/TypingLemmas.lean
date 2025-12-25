import Mathlib.Tactic.Lemma
import LocalLang.Typing

def Env.respectsTypeContext (V : Env) (Γ : TypeContext) : Prop :=
  ∀ (x : String) (ty : LLType), Γ[x]? = some ty
  → ∃ v, V[x]? = some v ∧ v.TypeJdg ty

lemma insert_preserves_env_respectsTypeContext {Γ : TypeContext} {V : Env} {v : Value}
  {v_ty : LLType} : V.respectsTypeContext Γ → v.TypeJdg v_ty →
  Env.respectsTypeContext (V.insert x v) (Γ.insert x v_ty) := by
  intro V_resp_Γ v_jdg x' ty' x'_in_Γ'
  rw [Std.HashMap.getElem?_insert] at *
  split
  · rename_i x_eq_x'
    simp only [x_eq_x', if_true] at x'_in_Γ'
    injection x'_in_Γ' with ty_eq
    exists v
    constructor
    · rfl
    · rw [← ty_eq]
      assumption
  · rename_i x_neq_x'
    apply V_resp_Γ
    simp only [x_neq_x'] at x'_in_Γ'
    assumption

lemma len_eq_of_typeJdgList (es : List Expr) (tys : List LLType) : Expr.TypeJdgList Γ es tys
  → tys.length = es.length := by
  intro tjlist
  induction tys generalizing es with
  | nil => cases tjlist; rfl
  | cons ty tys' ih =>
    cases es <;> cases tjlist
    rename_i e es' e_jdg es'_jdg
    simp [ih es' es'_jdg]
