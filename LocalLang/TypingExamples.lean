import LocalLang.Typing

-- Examples for TypeJdg
example : TypeJdg [] (.const 5) .nat := by
  apply TypeJdg.jdgConst

example : TypeJdg [("x", .nat)] (.var "x") .nat := by
  apply TypeJdg.jdgVar (List.mem_singleton_self ("x", LLType.nat))

def ctx : TypeContext := [("add", .func [.nat] .nat), ("x", .nat)]

example : TypeJdg ctx (.funCall "add" [.var "x"]) (LLType.func [.nat] .nat) := by
  apply TypeJdg.jdgFun (by simp [ctx]) (by
    apply TypeJdgList.cons
    · apply TypeJdg.jdgVar
      simp [ctx]
    · apply TypeJdgList.nil
  )
