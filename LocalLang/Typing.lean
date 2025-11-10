import LocalLang.AST
import LocalLang.Types

-- in context Γ expression ε has Type T

mutual
  inductive TypeJdg : TypeContext → Expr → LLType → Prop where
    | jdgVar {Γ : TypeContext}  {name : String} (H : (name, LLType.nat) ∈ Γ)
                      : TypeJdg Γ (.var name) LLType.nat
    | jdgConst {Γ : TypeContext} {n : ℕ} : TypeJdg Γ (.const n) LLType.nat
    | jdgFun {Γ : TypeContext} {es : List Expr} {arg_types : List LLType} {T_return : LLType}
                  (H_f : (f, .func arg_types T_return) ∈ Γ)
                  (H_args : TypeJdgList Γ es arg_types)
                        : TypeJdg Γ (.funCall f es) (LLType.func arg_types T_return)

  inductive TypeJdgList : TypeContext -> List Expr -> List LLType -> Prop
    | nil : TypeJdgList Γ [] []
    | cons {e : Expr} {T : LLType} {es : List Expr} {Ts : List LLType}
          (h_e : TypeJdg Γ e T) (h_es : TypeJdgList Γ es Ts)
          : TypeJdgList Γ (e :: es) (T :: Ts)
end
