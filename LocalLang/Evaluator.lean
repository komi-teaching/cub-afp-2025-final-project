import LocalLang.AST
import Mathlib.Control.Traversable.Basic

def BinOp.eval : BinOp → ℕ → ℕ → ℕ
  | add, x, y => x + y
  | mul, x, y => x * y

partial def Expr.eval (V : Env) : Expr → Option Value := sorry

partial def evaluate (prog : Program) : Option Value := prog.main.eval prog.env
