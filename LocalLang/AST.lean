import Mathlib.Data.Nat.Notation
import Std.Data.HashMap.Basic

inductive BinOp where
  | add
  | mul

inductive Expr where
  | const (n : ℕ)
  | var (name : String)
  | binOp (op : BinOp) (e₁ e₂ : Expr)
  | letIn (name : String) (e₁ e₂ : Expr)
  | funCall (f : String) (es : List Expr)

structure Func where
  parameters : List String
  body : Expr

abbrev Definitions := Std.HashMap String Func

structure Program where
  definitions : Definitions
  main : Expr

abbrev Env := Std.HashMap String ℕ
