import LocalLang.AST
import Std.Data.HashMap.Basic
import Init.Data.Repr

abbrev Vars := Std.HashMap String ℕ

inductive Computation (α : Type) where
  | ret (val : α) : Computation α
  | fail : Computation α
  | outOfGas : Computation α
deriving Repr

def Computation.bind {α β} (c : Computation α) (f : α → Computation β) : Computation β :=
  match c with
  | Computation.ret a => f a
  | Computation.fail  => Computation.fail
  | Computation.outOfGas => Computation.outOfGas

instance : Monad Computation where
  pure := Computation.ret
  bind := Computation.bind

def BinOp.eval : BinOp → ℕ → ℕ → ℕ
  | add, x, y => x + y
  | mul, x, y => x * y

def Function.bindArgs (func : Function) (args : List ℕ) (V : Vars) : Vars :=
  let param_arg_list := List.zip func.parameters args
  param_arg_list.foldl (fun acc (name, value) => acc.insert name value) V

def Expr.eval (gas : ℕ) (V : Vars) (D : Definitions) (e : Expr) : Computation ℕ :=
  match gas with
  | 0 => Computation.outOfGas
  | gas' + 1 =>
    match e with
    | const k =>
        return k

    | var x =>
        match V[x]? with
        | some v => return v
        | none   => Computation.fail

    | binOp op e₁ e₂ => do
        let v₁ ← e₁.eval gas' V D
        let v₂ ← e₂.eval gas' V D
        return (op.eval v₁ v₂)

    | funCall ef es => do
        let args ← es.mapM (fun e => e.eval gas' V D)
        match D[ef]? with
        | none => Computation.fail
        | some func =>
            let V_with_args := Function.bindArgs func args V
            -- Crucial: We call recursively with `gas'`, which is strictly smaller than `gas`.
            func.body.eval gas' V_with_args D

-- ---------------------------------------------------------
-- 4. Running
-- ---------------------------------------------------------

def Program.evaluate (prog : Program) (fuel : ℕ) : Computation ℕ :=
  prog.main.eval fuel Std.HashMap.empty prog.definitions

def loopFunc : Function := {
  parameters := ["x"],
  body := Expr.funCall "loop" [Expr.var "x"]
}

def loopProg : Program := {
  definitions := Std.HashMap.empty.insert "loop" loopFunc,
  main := Expr.funCall "loop" [Expr.const 1]
}

-- Returns: Computation.outOfGas
#eval loopProg.evaluate 100
