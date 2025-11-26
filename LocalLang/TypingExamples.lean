import LocalLang.Typing

-- Examples for TypeJdg
example : TypeJdg {} (.const 5) .nat := by
  apply TypeJdg.jdgConst

example : TypeJdg {("x", .nat)} (.var "x") .nat := by
  apply TypeJdg.jdgVar
  simp

def ctx : TypeContext := {("add", .func [.nat] .nat), ("x", .nat)}

example : TypeJdg ctx (.funCall "add" [.var "x"]) (LLType.func [.nat] .nat) := by
  apply TypeJdg.jdgFun
  · simp [ctx]
  · sorry
