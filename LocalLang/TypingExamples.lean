import LocalLang.Typing

-- Examples for TypeJdg
example : Expr.TypeJdg {} (Expr.const 5) .nat := by
  apply Expr.TypeJdg.jdg_const

example : Expr.TypeJdg {("x", .nat)} (.var "x") .nat := by
  apply Expr.TypeJdg.jdg_var
  simp

def ctx : TypeContext := {("add", .func [.nat] .nat), ("x", .nat)}

example : Expr.TypeJdg ctx (.funCall (.var "add") [.var "x"]) (LLType.func [.nat] .nat) := by
  apply Expr.TypeJdg.jdg_fun
  · apply Expr.TypeJdg.jdg_var
    simp [ctx]
  · constructor
    · constructor
      simp [ctx, Std.HashMap.getElem_insert]
    · constructor
