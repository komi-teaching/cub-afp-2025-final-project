import LocalLang.AST
import LocalLang.Evaluator
import LocalLang.Semantics
import LocalLang.SemanticsLemmas
import LocalLang.Ctx

/--
We must prove Computation is a LawfulMonad to use standard library lemmas
like `List.mapM_cons`, which simplify `mapM` from its tail-recursive implementation.
-/
instance : LawfulMonad Computation where
  pure_bind := by
    intros; simp [bind, Computation.bind]
  bind_assoc := by
    intros α β γ x f g
    cases x <;> simp [bind, Computation.bind]
  bind_pure_comp := by
    intros α β f x
    cases x <;> simp [Functor.map, bind, pure, Computation.bind]
  bind_map := by
    intros; rfl
  id_map := by
    intros α x
    cases x <;> simp [Functor.map, Computation.bind]
  map_const := by
    intros; rfl
  seqLeft_eq := by
    intros α β x y
    cases x <;>
    cases y <;>
    simp [SeqLeft.seqLeft, Seq.seq, Functor.map, Computation.bind]
  seqRight_eq := by
    intros α β x y
    cases x <;>
    cases y <;>
    simp [SeqRight.seqRight, Seq.seq, Functor.map, Computation.bind]
  pure_seq := by
    intros α β g x
    simp [Seq.seq, Functor.map, Computation.bind]

/--
Helper: mapM is monotonic with respect to the monadic function.
We use `List.mapM_cons` (enabled by LawfulMonad) to structurally decompose the mapM.
-/
theorem mapM_monotonic {α β} {f g : α → Computation β} {xs : List α} {ys : List β}
  (h_mono : ∀ x v, f x = .result v → g x = .result v)
  (h_map : xs.mapM f = .result ys)
  : xs.mapM g = .result ys := by
  induction xs generalizing ys
  case nil =>
    -- mapM [] reduces to pure []
    simp [List.mapM] at h_map
    -- 'cases' unifies pure [] = result ys, implying ys = []
    cases h_map
    rfl

  case cons x xs ih =>
    -- Use the standard lemma to unfold mapM nicely
    rw [List.mapM_cons] at h_map
    rw [List.mapM_cons]

    -- Simplify binds in the hypothesis
    simp [bind, pure, Computation.bind] at h_map ⊢

    -- Destruct head evaluation (f x)
    match h_fx : f x with
    | .result y =>
      simp [h_fx] at h_map

      -- Destruct tail evaluation (mapM xs f)
      match h_tail : xs.mapM f with
      | .result tail_ys =>
        simp [h_tail] at h_map

        -- Now h_map is `Computation.result (y :: tail_ys) = Computation.result ys`
        -- 'cases' robustly handles the constructor equality and substitution
        cases h_map

        -- Apply monotonicity to head and tail
        rw [h_mono x y h_fx]
        rw [ih h_tail]

      | .fail => simp [h_tail] at h_map
      | .outOfGas => simp [h_tail] at h_map

    | .fail => simp [h_fx] at h_map
    | .outOfGas => simp [h_fx] at h_map

/--
Evaluation is monotonic with respect to fuel:
If we get a result with `gas`, we get the same result with `gas + k`.
-/
theorem eval_monotonic {e : Expr} {V : Env} {v : Value} {gas gas' : ℕ}
  (h : e.eval gas V = .result v)
  (h_gas : gas ≤ gas') : e.eval gas' V = .result v := by
  induction gas generalizing e V v gas'
  case zero =>
    -- gas = 0 implies eval = outOfGas, which cannot equal .result v
    simp [Expr.eval] at h
  case succ gas ih =>
    cases gas'
    case zero =>
      -- Contradiction: gas + 1 ≤ 0 is impossible
      cases h_gas
    case succ gas'' =>
      have h_le : gas ≤ gas'' := Nat.le_of_succ_le_succ h_gas

      -- Destruct 'e' to access sub-expressions
      cases e <;> simp [Expr.eval] at h ⊢

      -- 1. Value
      · exact h

      -- 2. Const
      · exact h

      -- 3. Var
      · split at h <;> simp_all

      -- 4. BinOp
      · rename_i op lhs rhs
        simp [bind, pure] at h
        match h₁ : lhs.eval gas V with
        | .result v₁ =>
          simp [h₁, Computation.bind] at h
          match h₂ : rhs.eval gas V with
          | .result v₂ =>
            simp [h₂] at h
            -- Apply IH to LHS and RHS
            rw [ih h₁ h_le]
            rw [ih h₂ h_le]
            simp [bind, pure, Computation.bind]
            exact h
          | .fail => simp [h₂] at h
          | .outOfGas => simp [h₂] at h
        | .fail => simp [h₁, Computation.bind] at h
        | .outOfGas => simp [h₁, Computation.bind] at h

      -- 5. LetIn
      · rename_i nm init body
        simp [bind] at h
        match h₁ : init.eval gas V with
        | .result v_init =>
          simp [h₁, Computation.bind] at h
          rw [ih h₁ h_le]
          simp [bind, Computation.bind]
          apply ih h h_le
        | .fail => simp [h₁, Computation.bind] at h
        | .outOfGas => simp [h₁, Computation.bind] at h

      -- 6. FunCall
      · rename_i fn args
        simp [bind] at h
        match h₁ : fn.eval gas V with
        | .result (.closure ps bd) =>
          simp [h₁, Computation.bind] at h
          rw [ih h₁ h_le]
          match h₂ : args.mapM (fun x => x.eval gas V) with
          | .result arg_vals =>
            simp [h₂] at h
            -- Pass the inductive hypothesis as the proof of element-wise monotonicity
            rw [mapM_monotonic (fun x v hx => ih hx h_le) h₂]
            simp [bind, Computation.bind]
            apply ih h h_le
          | .fail => simp [h₂] at h
          | .outOfGas => simp [h₂] at h
        | .result (.nat _) => simp [h₁, Computation.bind] at h
        | .fail => simp [h₁, Computation.bind] at h
        | .outOfGas => simp [h₁, Computation.bind] at h
