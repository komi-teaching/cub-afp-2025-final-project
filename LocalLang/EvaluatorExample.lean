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

-- Returns: Computation.result 1
#eval constProg.evaluate 100
