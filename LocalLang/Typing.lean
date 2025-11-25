import LocalLang.AST
import LocalLang.Types

-- in context Γ expression ε has Type T

mutual
  inductive TypeJdg : TypeContext → Expr → LLType → Prop where
    | jdgVar {Γ : TypeContext}  {name : String} {ty : LLType} (H : Γ[name]? = some ty)
                      : TypeJdg Γ (.var name) ty
    | jdgConst {Γ : TypeContext} {n : ℕ} : TypeJdg Γ (.const n) LLType.nat
    | jdgFun {f} {Γ : TypeContext} {es : List Expr} {arg_types : List LLType} {T_return : LLType}
                  (H_f : Γ[f]? = some (.func arg_types T_return))
                  (H_args : TypeJdgList Γ es arg_types)
                        : TypeJdg Γ (.funCall f es) (LLType.func arg_types T_return)
    | jdgBinOp {Γ : TypeContext} {op : BinOp} {e₁ e₂ : Expr}
                (H₁ : TypeJdg Γ e₁ LLType.nat) (H₂ : TypeJdg Γ e₂ LLType.nat)
                        : TypeJdg Γ (.binOp op e₁ e₂) .nat
    | jdgLetIn {Γ : TypeContext} {name : String} {e₁ e₂ : Expr} {ty₁ ty₂ : LLType}
                (H₁ : TypeJdg Γ e₁ ty₁)
                (H₂ : TypeJdg (Γ.insert name ty₁) e₂ ty₂)
                        : TypeJdg  Γ (.letIn name e₁ e₂) ty₂


  inductive TypeJdgList : TypeContext -> List Expr -> List LLType -> Prop
    | nil : TypeJdgList Γ [] []
    | cons {e : Expr} {T : LLType} {es : List Expr} {Ts : List LLType}
          (h_e : TypeJdg Γ e T) (h_es : TypeJdgList Γ es Ts)
          : TypeJdgList Γ (e :: es) (T :: Ts)
end
