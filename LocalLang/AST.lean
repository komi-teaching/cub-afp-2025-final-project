import Mathlib.Data.Nat.Notation
import Std.Data.HashMap.Basic

inductive BinOp where
  | add
  | mul

def BinOp.eval (n₁ n₂ : ℕ) : BinOp → ℕ
  | add => n₁ + n₂
  | mul => n₁ * n₂

inductive Expr where
  | const (n : ℕ)
  | var (name : String)
  | binOp (op : BinOp) (e₁ e₂ : Expr)
  | letIn (name : String) (e₁ e₂ : Expr)
  | funCall (f : String) (es : List Expr)

structure Function where
  name : String
  parameters : List String
  body : Expr

abbrev Definitions := Std.HashMap String Function

structure Program where
  definitions : Definitions
  main : Expr
