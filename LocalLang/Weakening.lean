import LocalLang.AST
import LocalLang.Semantics
import LocalLang.Types
import LocalLang.Typing

def TypeContext.subcontext (Γ₁ Γ₂ : TypeContext) : Prop :=
  ∀ (name : String) (ty : LLType), Γ₁[name]? = some ty → Γ₂[name]? = some ty

theorem subcontext_insert {Γ₁ Γ₂ : TypeContext} {name : String} {ty : LLType}
    (h : TypeContext.subcontext Γ₁ Γ₂) :
    TypeContext.subcontext (Γ₁.insert name ty) (Γ₂.insert name ty) := by
    simp [TypeContext.subcontext]
    intro name_x ty_x lookup_x
    rw [Std.HashMap.getElem?_insert]
    rw [Std.HashMap.getElem?_insert] at lookup_x
    simp [TypeContext.subcontext] at h
    split <;> simp_all

theorem Empty_subcontext (Γ : TypeContext) : TypeContext.subcontext {} Γ
    := by simp [TypeContext.subcontext]

mutual
  theorem weakening_expr {Γ₁ Γ₂ : TypeContext} {e : Expr} {ty : LLType}
        (H_sub : TypeContext.subcontext Γ₁ Γ₂)
        (H_jdg : Expr.TypeJdg Γ₁ e ty)
        : Expr.TypeJdg Γ₂ e ty := by
    match H_jdg with
    | .jdg_value h_val => exact Expr.TypeJdg.jdg_value h_val
    | .jdg_var h_lookup => apply Expr.TypeJdg.jdg_var
                           rename_i name
                           exact H_sub name ty h_lookup
    | .jdg_const => constructor
    | .jdg_fun f_jdg H_args => apply Expr.TypeJdg.jdg_fun
                               · exact weakening_expr H_sub f_jdg
                               · exact weakening_list H_sub H_args
    | .jdg_binOp H₁ H₂ => apply Expr.TypeJdg.jdg_binOp
                          · exact weakening_expr H_sub H₁
                          · exact weakening_expr H_sub H₂
    | .jdg_let_in H₁ H₂ => apply Expr.TypeJdg.jdg_let_in
                           · exact weakening_expr H_sub H₁
                           · apply weakening_expr (subcontext_insert H_sub) H₂

theorem weakening_list {Γ₁ Γ₂ : TypeContext} {es : List Expr} {tys : List LLType}
        (H_sub : TypeContext.subcontext Γ₁ Γ₂)
        (H_jdg : Expr.TypeJdgList Γ₁ es tys)
        : Expr.TypeJdgList Γ₂ es tys := by
    match H_jdg with
    | .nil => constructor
    | .cons h_e h_es => exact Expr.TypeJdgList.cons
                              (weakening_expr H_sub h_e) (weakening_list H_sub h_es)

end
