import LocalLang.AST

def BinOp.eval (n₁ n₂ : ℕ) : BinOp → ℕ
  | add => n₁ + n₂
  | mul => n₁ * n₂

-- Maybe `m ℕ` for some monad `m`?
-- TODO: implement
partial def evaluate : Program → ℕ := sorry
