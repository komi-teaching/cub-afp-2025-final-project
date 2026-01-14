import Lean
import Lean.PrettyPrinter
import LocalLang.Typing
import Init.Prelude

open Lean Meta Elab Tactic

elab "typejdg_cases" : tactic => do
  withMainContext do
    let context ← getLCtx
    for h in context do
      let type ← h.fvarId.getType
      let userName ← h.fvarId.getUserName
      if h.isImplementationDetail then
        continue
      let (fn, args) := type.getAppFnArgs
      if !fn = ``Expr.TypeJdg then
        continue
      let e := args[1]!
      if e.isApp then
        logInfo m!"{userName.toString} is of the correct form"
        let hExpr := Expr.fvar h.fvarId
        let eTerm : TSyntax `Lean.Parser.Tactic.elimTarget := ⟨← PrettyPrinter.delab hExpr⟩
        evalTactic (← `(tactic| cases $eTerm))

-- example (a : Expr.TypeJdg Γ (Expr.value v₁) LLType.nat) : False := by
--   typejdg_cases
--   sorry
