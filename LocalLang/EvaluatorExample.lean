import LocalLang.Evaluator

private def loopFuncBody : Expr := Expr.funCall (Expr.var "loop") [Expr.var "x"]
private def loopFunc : Value := Value.closure ["x"] loopFuncBody

private def loopProg : Program := {
  env := Std.HashMap.emptyWithCapacity.insert "loop" loopFunc,
  main := Expr.funCall (Expr.value loopFunc) [Expr.const 1]
}

-- Returns: Computation.outOfGas
#eval loopProg.evaluate 100

def constProg : Program := {
  env := Std.HashMap.emptyWithCapacity,
  main := Expr.const 1
}

-- Returns: Computation.result (Value.nat 1)
#eval constProg.evaluate 100

private def addProg : Program := {
  env := Std.HashMap.emptyWithCapacity,
  main := Expr.binOp .add (Expr.const 5) (Expr.const 7)
}

-- Returns: Computation.result (Value.nat 12)
#eval addProg.evaluate 10

private def letInProg : Program := {
  env := Std.HashMap.emptyWithCapacity,
  main := Expr.letIn "a" (Expr.const 10) (
    Expr.binOp .mul (Expr.var "a") (Expr.const 3)
  )
}

-- Returns: Computation.result (Value.nat 30)
#eval letInProg.evaluate 100

private def addOneBody : Expr := Expr.binOp .add (Expr.var "x") (Expr.const 1)
private def addOneFunc : Value := Value.closure ["x"] addOneBody

private def addOneProg : Program := {
  env := Std.HashMap.emptyWithCapacity.insert "addOne" addOneFunc,
  main := Expr.funCall (Expr.var "addOne") [Expr.const 41]
}

-- Returns: Computation.result (Value.nat 42)
#eval addOneProg.evaluate 100

private def sumAndMultiplyBody : Expr := Expr.binOp .mul
  (Expr.binOp .add (Expr.var "a") (Expr.var "b"))
  (Expr.var "c")

private def sumAndMultiplyFunc : Value := Value.closure ["a", "b"] sumAndMultiplyBody

private def multiArgProg : Program := {
  env := Std.HashMap.emptyWithCapacity
    |>.insert "c" (Value.nat 10)
    |>.insert "f" sumAndMultiplyFunc,
  -- Call f(2, 3) which evaluates to (2 + 3) * 10 = 50
  main := Expr.funCall (Expr.var "f") [Expr.const 2, Expr.const 3]
}

-- Returns: Computation.result 50
#eval multiArgProg.evaluate 100

private def unboundVarProg : Program := {
  env := Std.HashMap.emptyWithCapacity,
  main := Expr.var "y"
}

-- Returns: Computation.fail
#eval unboundVarProg.evaluate 10

private def badBody : Expr := Expr.const 1
private def badFunc : Value := Value.closure ["x"] badBody

private def typeMismatchProg : Program := {
  env := Std.HashMap.emptyWithCapacity.insert "f" badFunc,
  -- Attempts 1 + f, which is an arithmetic operation on a number and a closure.
  main := Expr.binOp .add (Expr.const 1) (Expr.var "f")
}

-- Returns: Computation.fail
#eval typeMismatchProg.evaluate 10

private def nonClosureCallProg : Program := {
  env := Std.HashMap.emptyWithCapacity,
  main := Expr.funCall (Expr.const 5) [Expr.const 1]
}

-- Returns: Computation.fail
#eval nonClosureCallProg.evaluate 10
