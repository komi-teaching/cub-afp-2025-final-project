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

def extractNatValue (e : Lean.Expr) (arg : Lean.Expr) : Option ℕ :=
  let nlit := if e.isAppOf ``Expr.value then
        if e.appArg!.isAppOf ``OfNat.ofNat then
          some e.appArg!.getAppArgs[1]!
        else if e.appArg!.isAppOf ``Value.nat then
          if e.appArg!.getAppArgs[0]!.isAppOf ``OfNat.ofNat then
            some e.appArg!.getAppArgs[0]!.getAppArgs[1]!
          else
            none
        else
          none
      else if e.isAppOf ``OfNat.ofNat then
        some arg.getAppArgs[1]!
      else
        none
  match nlit with
    | some (Lean.Expr.lit (Lean.Literal.natVal x)) => some x
    | _ => none

def wrapNatMetaMExpr (n : ℕ) : MetaM Lean.Expr :=
  mkAppM ``Value.nat #[Lean.Expr.lit (Lean.Literal.natVal n)]


partial def getListElements (e : Lean.Expr) : MetaM (Option (List Lean.Expr)) := do
  let e ← whnf e
  if e.isAppOf ``List.cons then
    let args := e.getAppArgs
    let head := args[1]!
    let tail := args[2]!
    match ← getListElements tail with
    | some tailElems => return some (head :: tailElems)
    | none => return none
  else if e.isAppOf ``List.nil then
    return some []
  else
    return none


/-
  Traverse `e` to find the next reduction step
  Return `some stx` where `stx` is the Syntax for the `Ctx` to use
-/
partial def findStepCtx (e : Lean.Expr) : MetaM (Option (TSyntax `term)) := do
  let (fn, args) := e.getAppFnArgs
  -- logInfo m!"[findStepCtx] Visiting: {fn}"

  -- 1. BINARY OPERATOR (HAdd -- sugared +, HMul -- *);
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

--def unbox_name(boxed : Lean.Expr) : String :=


/-
  Try to solve "defs[<NAME>] = ..." goal for function definitions
-/
elab "solve_fun_def" : tactic => do
  withMainContext do
    let target <- getMainTarget

    let (_, args) := target.getAppFnArgs
    let name_boxed_opt: Option Lean.Expr := args[1]?
    match name_boxed_opt with
      | some (Lean.Expr.app innerApp _) =>
        match innerApp with
          | Lean.Expr.app _ name =>
            --logInfo m!"[Inner] Found name: {name}"
            let nameStx ← PrettyPrinter.delab name
            evalTactic (←
              `(tactic| apply (Std.HashMap.getElem_ofList_of_mem (k := $nameStx)) <;> simp))
          | _ => throwError "Found app, but something is wrong"
      | _ => throwError "Can't find fun def usage part"
/-
  Try to solve `HeadSmallStep` goal:
  Attempts every constructor of `HeadSmallStep` and simplifies the results
-/
syntax "solve_head" : tactic

macro_rules
| `(tactic| solve_head) => `(tactic|
    first
    -- 1. Constants
    | apply HeadSmallStep.const_step

    -- 2. Variables
    | apply HeadSmallStep.var_step
      simp [Ctx.updateEnv, Std.HashMap.getElem_insert, *]

    -- 3. Binary Operations
    | apply HeadSmallStep.bin_op_step
      rfl

    -- 4. Let bindings
    | apply HeadSmallStep.let_in_const_step

    -- 5. Function calls
    | apply HeadSmallStep.fun_step rfl rfl
      try simp [*]
  )

syntax "machine_step" : tactic

macro_rules
| `(tactic| machine_step) => `(tactic|
    first
    | step_auto_context
      solve_head
      try rfl
      try solve_fun_def -- probably should put this only on functions
)

/-
  Symbolically looks up a string key in a HashMap expression.
  WIP
-/
partial def symbolicLookup (env : Lean.Expr) (key : String) : MetaM (Option Lean.Expr) := do
  logInfo m!"[SymbolicLookup]: env:{env}, key:{key}"
  if env.isAppOf ``Std.HashMap.insert then
    let args := env.getAppArgs
    logInfo m!"[SymbolicLookup]: args:{args}"
    let keyExpr := args[5]!
    let valExpr := args[6]!
    let rest    := args[4]!
    logInfo m!"[SymbolicLookup]: keyExpr:{keyExpr}, valExpr:{valExpr}, rest:{rest}"

    let keyExpr ← whnf keyExpr
    match keyExpr with
    | Lean.Expr.lit (Lean.Literal.strVal k) =>
      if k == key then return some valExpr
      else symbolicLookup rest key
    | _ => return none -- Can't determine key statically
  else
     return none -- TODO: Try to implement more cases...

/-
  Traverses `e` to find the redex and returns the REDUCED expression.
  Tracks the environment `currentEnv` to handle `let` scopes.
-/
partial def findAndReduce (currentEnv : Lean.Expr) (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let (fn, args) := e.getAppFnArgs
  logInfo m!"[FAR]: e: {e}, fn: {fn}, args: {args}"
  -- 1. BINARY OPERATOR
  if fn = ``Expr.binOp || fn = ``HAdd.hAdd || fn = ``HMul.hMul then
    let (op, e1, e2) :=
      if fn = ``Expr.binOp then (args[0]!, args[1]!, args[2]!)
      else
        let e1_raw := args[args.size - 2]!
        let e2_raw := args[args.size - 1]!
        if fn = ``HAdd.hAdd then
          (mkConst ``BinOp.add, e1_raw, e2_raw)
        else
          (mkConst ``BinOp.mul, e1_raw, e2_raw)
    logInfo m!"[FAR:BINOP]: op:{op}, e1:{e1}, e2:{e2}"

    if !isValueForTactic e1 then
      logInfo m!"[FAR:BINOP:LHS]: env:{currentEnv}, e:{e1}"
      match ← findAndReduce currentEnv e1 with
      | some e1' =>
        if fn = ``HAdd.hAdd then mkAppM ``HAdd.hAdd #[e1', e2]
        else if fn = ``HMul.hMul then mkAppM ``HMul.hMul #[e1', e2]
        else mkAppM ``Expr.binOp #[op, e1', e2]
      | none => return none
    else if !isValueForTactic e2 then
      logInfo m!"[FAR:BINOP:RHS]: env:{currentEnv}, e:{e2}"
      match ← findAndReduce currentEnv e2 with
      | some e2' =>
        if fn = ``HAdd.hAdd then mkAppM ``HAdd.hAdd #[e1, e2']
        else if fn = ``HMul.hMul then mkAppM ``HMul.hMul #[e1, e2']
        else mkAppM ``Expr.binOp #[op, e1, e2']
      | none => return none
    else
      logInfo m!"[FAR:BINOP:REDUCE]: op:{op}, e1:{e1}, e2:{e2}"
      let m_v_e1 := extractNatValue e1 (args[(args.size - 2)]!)
      let m_v_e2 := extractNatValue e2 (args[(args.size - 1)]!)

      logInfo m!"[FAR:BINOP:REDUCE]: e1 is actually {m_v_e1}"
      logInfo m!"[FAR:BINOP:REDUCE]: e2 is actually {m_v_e2}"

      let resNat: Option ℕ := match (m_v_e1, m_v_e2) with
      | (some n1, some n2) => match op with
        | Lean.Expr.const ``BinOp.mul _ => some (BinOp.eval BinOp.mul n1 n2)
        | Lean.Expr.const ``BinOp.add _ => some (BinOp.eval BinOp.add n1 n2)
        | _ => none
      | (_, _) => none
      logInfo m!"[FAR:BINOP:REDUCE]: e1 op e2 result: {resNat}"
      match resNat with
      | some n1 => mkAppM ``Expr.value #[← wrapNatMetaMExpr n1]
      | none => return none

  -- 2. LET IN
  else if fn = ``Expr.letIn then
    let (name, e1, e2) := (args[0]!, args[1]!, args[2]!)
    logInfo m!"[FAR:LET_IN]: name: {name}, e1: {e1}, e2: {e2}"
    if !isValueForTactic e1 then
      logInfo m!"[FAR:LET_IN:EXPR]"
      match ← findAndReduce currentEnv e1 with
      | some e1' => mkAppM ``Expr.letIn #[name, e1', e2]
      | none => return none
    else if !isValueForTactic e2 then
      logInfo m!"[FAR:LET_IN:BODY]"
      let m_v_e1 := extractNatValue e1 args[(args.size - 2)]!
      logInfo m!"[FAR:LET_IN:BODY]: expr is {m_v_e1}"
      match m_v_e1 with
        | some x =>
          let leExpr := ← wrapNatMetaMExpr x
          let newEnv ← mkAppM ``Std.HashMap.insert #[currentEnv, name, leExpr]
          let callRes ← findAndReduce newEnv e2
          logInfo m!"[FAR:LET_IN:BODY]: callRes: {callRes}"
          match callRes with
            | some e2' => mkAppM ``Expr.letIn #[name, e1, e2']
            | none => return none
        | none => return none

    else
      logInfo m!"[FAR:LET_IN:REDUCE]"
      return some e2

  -- 3. FUNCTION CALL
  else if fn = ``Expr.funCall then
    let (func, argsList) := (args[0]!, args[1]!)
    logInfo m!"[FAR:FUN_CALL]: func: {func}, argsList: {argsList}"
    if !isValueForTactic func then
      logInfo m!"[FAR:FUN_CALL:BODY]"
      let funcRed ← findAndReduce currentEnv func
      logInfo m!"[FAR:FUN_CALL:BODY] currentEnv: {currentEnv}, func: {func}, funcRed: {funcRed}"
      match funcRed with
      | some func' => mkAppM ``Expr.funCall #[func', argsList]
      | none => return none
    else
      logInfo m!"[FAR:FUN_CALL:REDUCE]"
      let closureVal := func.appArg!
      let ps := closureVal.getAppArgs[0]!
      let body := closureVal.appArg!
      let ps_expr ← getListElements ps
      let argsList_expr ← getListElements argsList
      logInfo m!"[FAR:FUN_CALL:REDUCE]: closureVal: {closureVal}, ps: {ps}, body: {body}, argsList: {argsList}"
      logInfo m!"[FAR:FUN_CALL:REDUCE]: ps_expr: {ps_expr}, argsList_expr: {argsList_expr}"

      match ps_expr, argsList_expr with
      | some params, some args =>
        let bindings := params.zip args
        let mut res := body
        for (name, val) in bindings do
           res ← mkAppM ``Expr.letIn #[name, val, res]
        return some res
      | _, _ =>
        return none


  -- 4. ATOMIC REDEXES (Var)
  else if fn = ``Expr.var || fn = ``Coe.coe then
    logInfo m!"[FAR:VAR]"
    let nameArg ← if fn = ``Coe.coe then pure args[2]! else pure args[0]!
    let name ← whnf nameArg
    logInfo m!"[FAR:VAR]: name: {name}"
    match name with
    | Lean.Expr.lit (Lean.Literal.strVal n) =>
      match ← symbolicLookup currentEnv n with
      | some val => mkAppM ``Expr.value #[val]
      | none => return none
    | _ => return none

  -- 5. Const
  else if fn = ``Expr.const then
    let n := args[0]!
    mkAppM ``Expr.value #[← mkAppM ``Value.nat #[n]]

  else
    return none

theorem to_rw : ∀ env: Env, ((Relation.ReflTransGen (SmallStep env)) = (SmallSteps env)) := by
  intro
  rfl

syntax "take_next_step" : tactic

elab_rules : tactic
| `(tactic| take_next_step) => do
  withMainContext do
    let target ← getMainTarget

    let (fn, args) := target.getAppFnArgs
    if !fn = ``SmallSteps then
      throwError "Goal must be SmallSteps"

    let env := args[0]!
    let lhs := args[1]!

    -- Calculate next step
    match ← findAndReduce env lhs with
    | some nextLhs =>
      -- We have A -> B, goal is A ->* Z.
      -- Apply `Relation.ReflTransGen.head (b := B)`
      -- This creates two subgoals: A -> B and B ->* Z.

      let nextLhsStx ← PrettyPrinter.delab nextLhs
      evalTactic (← `(tactic| apply Relation.ReflTransGen.head (b := $nextLhsStx)))

    | none =>
      throwError "Could not calculate next step for: {lhs}"


syntax "machine_solve" : tactic

macro_rules
| `(tactic| machine_solve) => `(tactic|
    first
    | repeat
        take_next_step
        · machine_step
        rw[to_rw]
      try rfl
)
