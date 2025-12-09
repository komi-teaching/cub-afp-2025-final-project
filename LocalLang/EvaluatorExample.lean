import LocalLang.Evaluator

private def loopFunc : Func := {
  parameters := ["x"],
  body := Expr.funCall "loop" [Expr.var "x"]
}

private def loopProg : Program := {
  definitions := Std.HashMap.emptyWithCapacity.insert "loop" loopFunc,
  main := Expr.funCall "loop" [Expr.const 1]
}

-- Returns: Computation.outOfGas
#eval loopProg.evaluate 100

def constProg : Program := {
  definitions := Std.HashMap.emptyWithCapacity,
  main := Expr.const 1
}

-- Returns: Computation.result 1
#eval constProg.evaluate 100
