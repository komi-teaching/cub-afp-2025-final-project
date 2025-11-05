import LocalLang.AST

-- def Vars := Std.HashMap String ℕ

def BinOp.eval : BinOp → ℕ → ℕ → ℕ
  | add, x, y => x + y
  | mul, x, y => x * y

def Function.inline (V : Std.HashMap String ℕ) : Function → List ℕ → (Std.HashMap String ℕ × Expr)
  | func, agrs =>
    let param_arg_list := List.zip func.parameters agrs
    let V_with_args := param_arg_list.foldl
      (fun acc (name, value) => acc.insert name value) V
    (V_with_args, func.body)

def List.nonnull : List (Option ℕ) → Option (List ℕ)
  | [] => some []
  | none :: _ => none
  | (some x) :: xs => do
    let ys <- List.nonnull xs
    some (x :: ys)

partial def Expr.eval (V : Std.HashMap String ℕ) : Expr → Option ℕ
  | const k => pure k
  | var x => V[x]?
  | binOp op e₁ e₂ => do
      let v₁ <- e₁.eval V
      let v₂ <- e₂.eval V
      pure (op.eval v₁ v₂)
  | funCall ef es => do
    let args_opt : List (Option ℕ) := es.map (fun (elm) => elm.eval V)
    let args : List ℕ <- args_opt.nonnull
    let (V_with_args, expr) := Function.inline V ef args
    let evaled := expr.eval V_with_args
    evaled

-- Maybe `m ℕ` for some monad `m`?
-- TODO: implement
partial def evaluate : Program → ℕ := sorry
