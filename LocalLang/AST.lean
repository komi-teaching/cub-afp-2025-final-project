import Mathlib.Data.Nat.Notation


inductive BinOp where
  | add
  | mul

inductive Expr where
  | const (n : ℕ)
  | var (name : String)
  | binOp (op : BinOp) (e₁ e₂ : Expr)
  | funCall (ef : Expr) (es : List Expr)

structure Function where
  parameters : List String
  body : Expr

def Definitions := List Function

structure Program where
  definitions : Definitions
  main : Expr
