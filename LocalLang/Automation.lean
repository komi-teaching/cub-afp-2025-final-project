import Lean
import Lean.PrettyPrinter
import LocalLang.Typing
import Lean.Elab.Binders
import Lean.Meta.CtorRecognizer

open Lean Meta Elab Tactic

def can_do_cases_on (h : LocalDecl) : MetaM Bool := do
  let type ← h.fvarId.getType
  let (fn, args) := type.getAppFnArgs
  let e := args[1]!
  return !h.isImplementationDetail && fn = ``Expr.TypeJdg && (← isConstructorApp e)

syntax (name := typejdg_cases) "typejdg_cases" (ppSpace colGt binderIdent)* : tactic

@[tactic «typejdg_cases»] def tj_cases : Tactic
  | `(tactic| typejdg_cases $hs*) => do
    withMainContext do
      let context ← getLCtx
      for h in context do
        if !(← can_do_cases_on h) then
          continue
        let hExpr := Expr.fvar h.fvarId
        let eTerm : TSyntax `Lean.Parser.Tactic.elimTarget ←
          `(Lean.Parser.Tactic.elimTarget| $(← PrettyPrinter.delab hExpr):term)
        evalTactic (← `(tactic| cases $eTerm))
      replaceMainGoal [← renameInaccessibles (← getMainGoal) hs]
  | _ => throwUnsupportedSyntax

example (var_jdg : Expr.TypeJdg Γ (.var "x") LLType.nat)
        (funCall_jdg : Expr.TypeJdg Γ (.funCall (.var "f") [.var "x"]) .nat) : False := by
  typejdg_cases -- successfully runs cases on both hypotheses
  sorry

example (const_jdg : Expr.TypeJdg Γ (.const 13) .nat) : False := by
  typejdg_cases -- runs cases on const_jdg, even though jdg_const has no arguments
  sorry

example (binop_jdg : Expr.TypeJdg Γ (.binOp .add e₁ e₂) .nat) : False := by
  typejdg_cases h₁ h₂ -- runs cases on binop_jdg and renames the new hypotheses
  sorry

def f (n : ℕ) : _root_.Expr := .var ("x" ++ n.toSubscriptString)

example (e_jdg₁ : Expr.TypeJdg Γ (f 1) .nat)
  (e_jdg₂ : Expr.TypeJdg Γ e LLType.nat) : False := by
  typejdg_cases -- does nothing
  sorry
