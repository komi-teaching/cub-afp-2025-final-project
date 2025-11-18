import LocalLang.Evaluator

-- test for updateEnv, ensures that existing values get overwritten correctly
example :=
  let V : Env := .ofList [("x", 1)]
  let func : Func := ⟨["x"], .const 0⟩
  let V' := func.updateEnv V [2]
  let result : V'["x"]? = some 2 := by
    unfold V'
    unfold V
    rw [Func.updateEnv, List.zip, List.zipWith, ← Std.HashMap.get?_eq_getElem?,
      Std.HashMap.get?_union]
    simp
  result
