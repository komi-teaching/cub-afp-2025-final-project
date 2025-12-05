import LocalLang.Semantics
import LocalLang.SemanticsLemmas
import LocalLang.Ctx
import Mathlib.Data.List.Sigma
import Std.Data.HashMap.Basic
import Std.Data.HashMap.Lemmas

instance : Add Expr where
  add := .binOp .add

instance : Coe String Expr where
  coe := .var

instance : OfNat Expr n where
  ofNat := .const n

abbrev f_body : Expr := (.funCall "g" [ "x" + 1 ]) + "x"
abbrev f : Value := .closure ["x"] f_body
abbrev g : Value := .closure ["x"] "x"

abbrev defs := Std.HashMap.ofList [("f", f), ("g", g)]

@[simp] lemma defs_f : defs["f"] = f := by
  apply (Std.HashMap.getElem_ofList_of_mem (k := "f")) <;> simp
@[simp] lemma defs_g : defs["g"] = g := by
  apply (Std.HashMap.getElem_ofList_of_mem (k := "g")) <;> simp

lemma f_steps
  : SmallSteps (defs.insert "x" 0)
      (Expr.funCall "g" ["x" + 1] + Expr.var "x") 1 := by
  sorry

example : SmallSteps defs (.funCall "f" [0]) 1 := by
  sorry
