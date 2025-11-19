import Mathlib.Tactic.DefEqTransformations

def DelayM (α : Type u) : Type u :=
  { f : Nat → Option α // ∀ n a, f n = some a → f n.succ = some a }

def DelayM.loop : DelayM α := ⟨fun _ => none, fun _ _ => id⟩
def DelayM.withDelay (a : α) (d : Nat) : DelayM α := ⟨
  fun n => if n < d then none else some a,
  fun n b h => by
    beta_reduce at h ⊢
    split at h <;> cases h
    split <;> try rfl
    rename_i h h'
    cases h (Nat.lt_of_succ_lt h')
⟩
def DelayM.ofOption (a : Option α) : DelayM α := ⟨
  Function.const _ a,
  fun n x h => by
    rw [Function.const] at h ⊢
    assumption
⟩

instance : Pure DelayM where
  pure a := DelayM.ofOption (pure a)

instance : Bind DelayM where
  bind x f := ⟨
    fun n => do
      let result <- x.val n
      (f result).val n
    ,
    fun n b h => by
      cases xn : x.val n
      case none => simp [xn, bind] at h
      case some a =>
        beta_reduce
        rw [x.property n a xn]
        apply (f a).property n b
        simp only [xn] at h
        assumption
  ⟩

instance : Monad DelayM where
