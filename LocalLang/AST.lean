import Mathlib.Data.Nat.Notation
import Std.Data.HashMap.Basic

inductive BinOp where
  | add
  | mul

mutual
inductive Value where
  | nat (n : ℕ)
  | closure (ps : List String) (body : Expr)

inductive Expr where
  | value (v : Value)
  | const (n : ℕ)
  | var (name : String)
  | binOp (op : BinOp) (e₁ e₂ : Expr)
  | letIn (name : String) (e₁ e₂ : Expr)
  | funCall (e : Expr) (es : List Expr)
end

instance : OfNat Value n where
  ofNat := .nat n

abbrev Env := Std.HashMap String Value

structure Program where
  env : Env
  main : Expr
