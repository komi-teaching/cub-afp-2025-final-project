import LocalLang.SemanticsLemmas
import Lean
import Lean.PrettyPrinter
import LocalLang.Semantics

open Lean Meta Elab Tactic

/-
  No need to step into values
-/
def isValueForTactic (e : Lean.Expr) : Bool :=
  e.isAppOf ``Expr.value || e.isAppOf ``OfNat.ofNat

def getValueSyntax (e : Lean.Expr) : MetaM (TSyntax `term) := do
  if e.isAppOf ``OfNat.ofNat then
    -- Case: OfNat.ofNat Expr n inst
    let args := e.getAppArgs
    let n := args[1]!
    let nStx : TSyntax `term := ⟨← PrettyPrinter.delab n⟩
    `(Value.nat $nStx)
  else
    -- Case: Expr.value v
    let v := e.appArg!
    let vStx : TSyntax `term := ⟨← PrettyPrinter.delab v⟩
    return vStx

/-
  Traverse `e` to find the next reduction step
  Return `some stx` where `stx` is the Syntax for the `Ctx` to use
-/
partial def findStepCtx (e : Lean.Expr) : MetaM (Option (TSyntax `term)) := do
  let (fn, args) := e.getAppFnArgs
  -- logInfo m!"[findStepCtx] Visiting: {fn}"

  -- 1. BINARY OPERATOR (HAdd -- sugared +); TODO: Add HMul?
  if fn = ``Expr.binOp || fn = ``HAdd.hAdd || fn = ``HMul.hMul then
    -- binOp (op : BinOp) (e₁ e₂ : Expr)
    let (op, e1, e2) :=
      if fn = ``Expr.binOp then
        (args[0]!, args[1]!, args[2]!)
      else
        let e1_raw := args[args.size - 2]!
        let e2_raw := args[args.size - 1]!
        if fn = ``HAdd.hAdd then
          (mkConst ``BinOp.add, e1_raw, e2_raw)
        else
          (mkConst ``BinOp.mul, e1_raw, e2_raw)

    if !isValueForTactic e1 then
      match ← findStepCtx e1 with
      | some inner =>
        let e2Stx : TSyntax `term := ⟨← PrettyPrinter.delab e2⟩

        if fn = ``HAdd.hAdd then -- need to put op manually
           return some (← `(Ctx.binOpLhs $inner BinOp.add $e2Stx))
        else if fn = ``HMul.hMul then -- same for mul
            return some (<- `(Ctx.binOpLhs $inner BinOp.mul $e2Stx))
        else
           let opStx : TSyntax `term := ⟨← PrettyPrinter.delab op⟩
           return some (← `(Ctx.binOpLhs $inner $opStx $e2Stx))
      | none => return none
    else
      if !isValueForTactic e2 then
        match ← findStepCtx e2 with
        | some inner =>
          let vStx ← getValueSyntax e1
          if fn = ``HAdd.hAdd then
             return some (← `(Ctx.binOpRhs $vStx BinOp.add $inner))
          else if fn = ``HMul.hMul then
              return some (<- `(Ctx.binOpRhs $vStx BinOp.mul $inner))
          else
             let opStx : TSyntax `term := ⟨← PrettyPrinter.delab op⟩
             return some (← `(Ctx.binOpRhs $vStx $opStx $inner))
        | none => return none
      else
        return some (← `(Ctx.hole))

  -- 2. LET IN
  else if fn = ``Expr.letIn then
    -- letIn (name : String) (e₁ e₂ : Expr)
    let name := args[0]!
    let e1 := args[1]!
    let e2 := args[2]!

    if !isValueForTactic e1 then
      match ← findStepCtx e1 with
      | some inner =>
        let nameStx ← PrettyPrinter.delab name
        let e2Stx ← PrettyPrinter.delab e2
        return some (← `(Ctx.letInExpr $nameStx $inner $e2Stx))
      | none => return none
    else
      if !isValueForTactic e2 then
        match ← findStepCtx e2 with
        | some inner =>
          let nameStx ← PrettyPrinter.delab name
          let vStx ← getValueSyntax e1
          return some (← `(Ctx.letInBody $nameStx $vStx $inner))
        | none => return none
      else
        return some (← `(Ctx.hole))

  -- 3. FUNCTION CALL
  else if fn = ``Expr.funCall then
    -- funCall (e : Expr) (es : List Expr)
    let func := args[0]!
    let argsList := args[1]!

    if !isValueForTactic func then
      match ← findStepCtx func with
      | some inner =>
        let argsStx ← PrettyPrinter.delab argsList
        return some (← `(Ctx.funCallBody $inner $argsStx))
      | none => return none
    else
      return some (← `(Ctx.hole))

  -- 4. ATOMIC REDEXES (Var, Const)
  else if fn = ``Expr.var then
    return some (← `(Ctx.hole))
  else if fn = ``Expr.const then
    return some (← `(Ctx.hole))

  else
    logWarning m!"[findStepCtx] Matched with nothing: {fn}"
    return none

/-
  Try to perform a single reduction step:
  1. Identify the expression to be reduced from the goal
  2. Find the evaluation context `ctx`
  3. Apply `SmallStep.ctx_step ctx rfl rfl`
-/
elab "step_auto_context" : tactic => do
  withMainContext do
    let target ← getMainTarget

    -- Deconstruct the goal
    let (fn, args) := target.getAppFnArgs

    if !fn = ``SmallStep then
      throwError "Tactic 'step_auto_context' only works on SmallStep goals."

    -- args[0] is env, args[1] is e1, args[2] is e2
    let e1 := args[1]!

    -- Use our helper to find the context syntax
    match ← findStepCtx e1 with
    | some ctxStx =>
      evalTactic (← `(tactic| apply SmallStep.ctx_step $ctxStx rfl rfl ?_))
    | none =>
      throwError "Could not find a reduction step for: {e1}"

/--
  Tactic to solve the `HeadSmallStep` goal automatically.
  It tries every constructor of `HeadSmallStep` and uses `simp` to handle
  environment lookups and arithmetic.
-/
syntax "solve_head" : tactic

macro_rules
| `(tactic| solve_head) => `(tactic|
    first
    -- 1. Constants (e.g. `1`)
    | apply HeadSmallStep.const_step

    -- 2. Variables (e.g. `x`)
    -- We use `simp` with `*` to use local definitions (like `let env := ...`)
    -- and the HashMap lemmas to find the value in the environment.
    | apply HeadSmallStep.var_step
      simp [Ctx.updateEnv, Std.HashMap.getElem_insert, *]

    -- 3. Binary Operations (e.g. `1 + 2`)
    -- `rfl` handles the arithmetic (e.g. 1+2 = 3).
    | apply HeadSmallStep.bin_op_step
      rfl

    -- 4. Let bindings (e.g. `let x = v in ...`)
    | apply HeadSmallStep.let_in_const_step

    -- 5. Function calls (e.g. `(fun x => ...)(v)`)
    -- We try to prove length equality and substitution with `rfl` or `simp`.
    | apply HeadSmallStep.fun_step rfl rfl
      try simp [*]
  )
