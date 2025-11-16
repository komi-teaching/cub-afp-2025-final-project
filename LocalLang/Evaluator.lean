import LocalLang.AST
import Mathlib.Control.Traversable.Basic

def BinOp.eval : BinOp → ℕ → ℕ → ℕ
  | add, x, y => x + y
  | mul, x, y => x * y

def Function.updateEnv (func : Function) (V : Env) (args : List ℕ) : Env :=
  let param_arg_list := List.zip func.parameters args
  V ∪ .ofList param_arg_list

-- test for updateEnv, ensures that existing values get overwritten correctly
example :=
  let V : Env := .ofList [("x", 1)]
  let func : Function := ⟨["x"], .const 0⟩
  let V' := Function.updateEnv func V [2]
  let result : V'["x"]? = some 2 := by
    unfold V'
    unfold V
    unfold func
    rw [Function.updateEnv, List.zip, List.zipWith, ← Std.HashMap.get?_eq_getElem?,
      Std.HashMap.get?_union]
    simp
  result

partial def Expr.eval (V : Env) (D : Definitions) : Expr → Option ℕ
  | const k => pure k
  | var x => V[x]?
  | binOp op e₁ e₂ => do
    let v₁ <- e₁.eval V D
    let v₂ <- e₂.eval V D
    pure (op.eval v₁ v₂)
  | funCall ef es => do
    let func <- D[ef]?
    let args_opt : List (Option ℕ) := es.map (·.eval V D)
    let args : List ℕ <- sequence args_opt
    let V_with_args := Function.updateEnv func V args
    func.body.eval V_with_args D
  | letIn x e body => do
    let vₓ <- e.eval V D
    body.eval (V.insert x vₓ) D

partial def evaluate (prog : Program) : Option ℕ := prog.main.eval ∅ prog.definitions
