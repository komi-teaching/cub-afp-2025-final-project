import LocalLang.AST

abbrev Vars := Std.HashMap String ℕ

def BinOp.eval : BinOp → ℕ → ℕ → ℕ
  | add, x, y => x + y
  | mul, x, y => x * y

def Function.inline (V : Vars) : Function → List ℕ → (Std.HashMap String ℕ × Expr)
  | func, agrs =>
    let param_arg_list := List.zip func.parameters agrs
    let V_with_args := param_arg_list.foldl
      (fun acc (name, value) => acc.insert name value) V
    (V_with_args, func.body)

def List.sequence : List (Option ℕ) → Option (List ℕ)
  | [] => some []
  | none :: _ => none
  | (some x) :: xs => do
    let ys <- List.sequence xs
    some (x :: ys)

partial def Expr.eval (V : Vars) (D : Definitions) : Expr → Option ℕ
  | const k => pure k
  | var x => V[x]?
  | binOp op e₁ e₂ => do
      let v₁ <- e₁.eval V D
      let v₂ <- e₂.eval V D
      pure (op.eval v₁ v₂)
  | funCall ef es => do
    let args_opt : List (Option ℕ) := es.map (fun (elm) => elm.eval V D)
    let args : List ℕ <- args_opt.sequence
    let func <- D[ef]?
    let (V_with_args, expr) := Function.inline V func args
    let evaled := expr.eval V_with_args D
    evaled

partial def evaluate : Program → Option ℕ
  | prog => prog.main.eval Std.HashMap.emptyWithCapacity prog.definitions
