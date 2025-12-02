import LocalLang.AST
import LocalLang.Types

-- in context Γ expression ε has Type T

mutual
  inductive Value.TypeJdg : Value → LLType → Prop where
    | jdg_nat : Value.TypeJdg (.nat n) .nat
    | jdg_closure {ps bd argTs retTy} : Expr.TypeJdg (.ofList (ps.zip argTs)) bd retTy →
      ps.length = argTs.length → Value.TypeJdg (.closure ps bd) (.func argTs retTy)


  inductive Expr.TypeJdg : TypeContext → Expr → LLType → Prop where
    | jdg_value {ty} : Value.TypeJdg v ty → Expr.TypeJdg Γ (.value v) ty
    | jdg_var {Γ : TypeContext} {name : String} {ty : LLType} (H : Γ[name]? = some ty)
                      : Expr.TypeJdg Γ (.var name) ty
    | jdg_const {Γ : TypeContext} {n : ℕ} : Expr.TypeJdg Γ (.const n) LLType.nat
    | jdg_fun {Γ : TypeContext} {es : List Expr} {arg_types : List LLType} {T_return : LLType}
                  (f_jdg : Expr.TypeJdg Γ f (.func arg_types T_return))
                  (H_args : Expr.TypeJdgList Γ es arg_types)
                        : TypeJdg Γ (.funCall f es) T_return
    | jdg_binOp {Γ : TypeContext} {op : BinOp} {e₁ e₂ : Expr}
                (H₁ : Expr.TypeJdg Γ e₁ LLType.nat) (H₂ : Expr.TypeJdg Γ e₂ LLType.nat)
                        : Expr.TypeJdg Γ (.binOp op e₁ e₂) .nat
    | jdg_let_in {Γ : TypeContext} {name : String} {e₁ e₂ : Expr} {ty₁ ty₂ : LLType}
                (H₁ : Expr.TypeJdg Γ e₁ ty₁)
                (H₂ : Expr.TypeJdg (Γ.insert name ty₁) e₂ ty₂)
                        : Expr.TypeJdg  Γ (.letIn name e₁ e₂) ty₂

  inductive Expr.TypeJdgList : TypeContext -> List Expr -> List LLType -> Prop
    | nil : Expr.TypeJdgList Γ [] []
    | cons {e : Expr} {T : LLType} {es : List Expr} {Ts : List LLType}
          (h_e : Expr.TypeJdg Γ e T) (h_es : Expr.TypeJdgList Γ es Ts)
          : Expr.TypeJdgList Γ (e :: es) (T :: Ts)
end
