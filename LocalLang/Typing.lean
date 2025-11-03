import LocalLang.AST
import LocalLang.Types

-- in context Γ expression ε has Type T
-- TODO: define
inductive TypeJdg : TypeContext → Expr → LLType → Prop where
  | Jdg_Var {Γ : TypeContext}  {name : String} (H : Γ.find? (·.1 = name) = some ⟨name, LLType.nat⟩) : TypeJdg Γ (.var name) LLType.nat
  | Jdg_Const {Γ : TypeContext} {n : ℕ} : TypeJdg Γ (.const n) LLType.nat
  | JdgFun {Γ : TypeContext} {es : List Expr} {arg_types : List LLType} {T_return : LLType}
                (H_f : Γ.find? (·.1 = f) = some ⟨f, .func arg_types T_return⟩)
                (H_args : List.zip es arg_types) -- I want to declare, ∀ e : es, type : arg_types -> TypeJdg Γ e type
                    : TypeJdg Γ (.funCall f es) (LLType.func arg_types T_return)
