import LocalLang.AST
import Std.Data.HashMap.Basic
import Init.Data.Repr

inductive Computation (α : Type) where
  | result (val : α) : Computation α
  | fail : Computation α
  | outOfGas : Computation α
deriving Repr

def Computation.bind {α β} (c : Computation α) (f : α → Computation β) : Computation β :=
  match c with
  | Computation.result a => f a
  | Computation.fail  => Computation.fail
  | Computation.outOfGas => Computation.outOfGas

instance : Monad Computation where
  pure := Computation.result
  bind := Computation.bind

def BinOp.eval : BinOp → ℕ → ℕ → ℕ
  | add, x, y => x + y
  | mul, x, y => x * y

def Env.bindArgs (env : Env) (argNames : List String) (argValues : List Value) : Env :=
  let param_arg_list := List.zip argNames argValues
  param_arg_list.foldl (fun acc (name, value) => acc.insert name value) env

def Expr.eval (gas : ℕ) (env : Env) (expr : Expr) : Computation Value :=
  match gas with
  | 0 => Computation.outOfGas
  | gas' + 1 =>
    match expr with
    | value v => return v
    | const k => return Value.nat k
    | var x =>
        match env[x]? with
        | some v => return v
        | none   => Computation.fail

    | binOp op e₁ e₂ => do
        let v₁ ← e₁.eval gas' env
        let v₂ ← e₂.eval gas' env
        match v₁, v₂ with
        | (Value.nat r₁), (Value.nat r₂) => return Value.nat (op.eval r₁ r₂)
        | _, _ => Computation.fail

    | letIn varName init expr => do
        let varValue ← init.eval gas' env
        let env' := env.insert varName varValue
        expr.eval gas' env'

    | funCall ef es => do
        let clos ← Expr.eval gas' env ef
        match clos with
        | Value.closure argNames functionBody => do
          let args ← es.mapM (fun e => e.eval gas' env)
          let envWithArgs := env.bindArgs argNames args
          functionBody.eval gas' envWithArgs
        | _ => Computation.fail

def Program.evaluate (prog : Program) (fuel : ℕ) : Computation Value :=
  Expr.eval fuel prog.env prog.main
