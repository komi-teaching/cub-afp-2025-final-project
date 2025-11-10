import LocalLang.AST
import LocalLang.Types

-- in context Γ expression ε has Type T

mutual
  inductive TypeJdg : TypeContext → Expr → LLType → Prop where
    | JdgVar {Γ : TypeContext}  {name : String} (H : (name, LLType.nat) ∈ Γ)
                      : TypeJdg Γ (.var name) LLType.nat
    | JdgConst {Γ : TypeContext} {n : ℕ} : TypeJdg Γ (.const n) LLType.nat
    | JdgFun {Γ : TypeContext} {es : List Expr} {arg_types : List LLType} {T_return : LLType}
                  (H_f : (f, .func arg_types T_return) ∈ Γ)
                  (H_args : TypeJdgList Γ es arg_types)
                        : TypeJdg Γ (.funCall f es) (LLType.func arg_types T_return)

  inductive TypeJdgList : TypeContext -> List Expr -> List LLType -> Prop
    | Nil : TypeJdgList Γ [] []
    | Cons {e : Expr} {T : LLType} {es : List Expr} {Ts : List LLType}
          (h_e : TypeJdg Γ e T) (h_es : TypeJdgList Γ es Ts)
          : TypeJdgList Γ (e :: es) (T :: Ts)
end


-- Examples for TypeJdg
example : TypeJdg [] (.const 5) .nat := by
  apply TypeJdg.JdgConst

example : TypeJdg [("x", .nat)] (.var "x") .nat := by
  apply TypeJdg.JdgVar (List.mem_singleton_self ("x", LLType.nat))

def ctx : TypeContext := [("add", .func [.nat] .nat), ("x", .nat)]

example : TypeJdg ctx (.funCall "add" [.var "x"]) (LLType.func [.nat] .nat) := by
  apply TypeJdg.JdgFun (by simp [ctx]) (by
    apply TypeJdgList.Cons
    · apply TypeJdg.JdgVar
      simp [ctx]
    · apply TypeJdgList.Nil
  )
