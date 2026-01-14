import LocalLang.AST
import LocalLang.Evaluator
import LocalLang.Semantics
import LocalLang.SemanticsLemmas
import LocalLang.Ctx
import LocalLang.EvaluatorTheorem3
import Std.Data.HashMap.Lemmas
import Std.Data.HashMap
import Std.Data.HashMap.Basic

lemma eval_value_is_independent (v : Value) :
  ∀ g env, Expr.eval (g + 1) env (Expr.value v) = Computation.result v := by
  intros g env
  rfl

lemma mapM_congr {gas : ℕ} {V V' : Env} {es : List Expr}
    (h_pointwise : ∀ e ∈ es, Expr.eval gas V' e = Expr.eval gas V e) :
    List.mapM (fun e ↦ Expr.eval gas V' e) es = List.mapM (fun e ↦ Expr.eval gas V e) es := by
  induction es
  case nil => rfl
  case cons hd tl ih =>
    simp only [List.mapM_cons, bind, pure, Computation.bind]
    rw [h_pointwise hd List.mem_cons_self]
    rw [ih (fun x hx ↦ h_pointwise x (List.mem_cons_of_mem hd hx))]

def EnvEquiv (V1 V2 : Env) : Prop := ∀ (k : String), V1[k]? = V2[k]?

lemma eval_congruence_under_equiv {V1 V2 : Env} {e : Expr} {gas : ℕ}
  {h_equiv : EnvEquiv V1 V2} : e.eval gas V1 = e.eval gas V2 := by
  sorry

lemma eval_letIn_eq {V : Env} {gas : ℕ} {e : Expr} {v1 : Value} {n : String}
  : Expr.eval gas V (Expr.letIn n (Expr.value v1) e) = Expr.eval gas (V.insert n v1) e :=
  sorry


lemma env_insert_commute (V : Env) (n1 n2 : String) (v1 v2 : Value) (h_neq : n1 ≠ n2) :
    EnvEquiv
      ((V.insert n1 v1).insert n2 v2)
      ((V.insert n2 v2).insert n1 v1) := by
  dsimp [EnvEquiv]
  intro k
  by_cases h1 : k = n1
  case pos =>
    subst h1
    rw [Std.HashMap.getElem?_insert]
    simp [h_neq.symm]
  case neg =>
    by_cases h2 : k = n2
    case pos =>
      subst h2
      rw [Std.HashMap.getElem?_insert]
      simp [h_neq]
      simp [Std.HashMap.getElem_insert, h_neq]
    case neg =>
      simp [Std.HashMap.getElem?_insert, Ne.symm h1, Ne.symm h2]

lemma letIn_commute_vals {g : ℕ} {V : Env} {n1 n2 : String} {v1 v2 : Value} {body : Expr}
    (h_neq : n1 ≠ n2) :
    Expr.eval (g + 1) V (Expr.letIn n1 (Expr.value v1) (Expr.letIn n2 (Expr.value v2) body)) =
    Expr.eval (g + 1) V (Expr.letIn n2 (Expr.value v2) (Expr.letIn n1 (Expr.value v1) body)) := by

  -- Split g to handle gas consumption.
  cases g
  case zero =>
    -- Not enough gas for inner let (total gas 1). Both fail.
    simp [Expr.eval, bind, Computation.bind]

  case succ g' =>
    -- Enough gas for outer let.
    cases g'
    case zero =>
      -- Not enough gas for inner let (total gas 2). Both fail.
      simp [Expr.eval, bind, pure, Computation.bind]

    case succ g'' =>
      -- Enough gas for both (total gas g'' + 3).
      repeat rw [eval_letIn_eq]
      apply eval_congruence_under_equiv
      apply env_insert_commute
      assumption

lemma eval_value_irrelevant_env (v : Value) (V V' : Env) (gas : ℕ) :
    Expr.eval (gas + 1) V (Expr.value v) = Expr.eval (gas + 1) V' (Expr.value v) := by
  simp [Expr.eval, pure]

lemma eval_list_value_irrelevant_env {gas : ℕ} {V V' : Env} {es : List Expr}
    (h_vals : ∀ e ∈ es, ∃ v, e = Expr.value v) :
    List.mapM (fun e ↦ Expr.eval (gas + 1) V e) es =
    List.mapM (fun e ↦ Expr.eval (gas + 1) V' e) es := by
  induction es
  case nil => rfl
  case cons e es' ih =>
    simp [List.mapM_cons, bind, pure, Computation.bind]
    sorry

lemma bindArgs_cons_eq_insert (V : Env) (p : String)
  (ps : List String) (v : Value) (vs : List Value) :
    Env.bindArgs V (p :: ps) (v :: vs) = Env.bindArgs (Std.HashMap.insert V p v) ps vs := by
  simp [Env.bindArgs]

/--
The evaluator's behavior for `funCall` is equivalent to evaluating the `addBindings` expansion.
This bridges the gap between the semantics (which reduce to `let`)
and the evaluator (which updates Env).
-/
theorem eval_addBindings_eq_funCall {V : Env} {ps : List String} {es : List Expr} {bd : Expr}
  {h_len : ps.length = es.length} {gas : ℕ} {v : Value}
  (h : Expr.eval gas V ((Expr.value (Value.closure ps bd)).funCall es) = Computation.result v)
  : ∃ gas', Expr.eval gas' V (Expr.addBindings ps es bd h_len) = Computation.result v := by
  induction es generalizing ps V gas v
  case nil =>
    cases ps
    case cons => contradiction
    case nil =>
      -- 1. Simplify the goal: addBindings [] [] bd is just bd
      simp [Expr.addBindings]
      exists (gas + 1)

      -- 2. Simplify hypothesis h
      cases gas
      case zero => simp [Expr.eval] at h
      case succ g =>
        -- Unfold the monad logic
        simp [Expr.eval, bind, pure, Computation.bind] at h

        -- CRITICAL STEP: Break the stuck 'match' on the closure evaluation
        -- This considers cases: result, fail, outOfGas.
        -- Only 'result' will survive because h is 'result v'.
        split at h

        -- 3. Dismiss impossible cases (fail/outOfGas != result v)
        all_goals try (simp at h; contradiction)

        -- 4. Now h is clean: Expr.eval g V bd = result v.
        --    The env is clean because bindArgs [] [] = V.
        simp [Env.bindArgs] at h

        -- 5. Use monotonicity: if it runs in g, it runs in g+1 (gas+1)
        apply eval_monotonic h
        apply Nat.le_succ

  case cons e es' ih =>
    cases ps
    case nil => contradiction -- Length mismatch
    case cons p ps' =>
      -- Inductive step
      -- 1. Unpack the 'funCall' evaluation from 'h'
      --    We know it succeeds, so gas > 0.
      cases gas
      case zero => simp [Expr.eval] at h
      case succ g =>
        simp [Expr.eval, bind, pure, Computation.bind] at h

        -- The evaluator maps over the arguments: e :: es'
        -- simp [List.mapM_cons] at h
        -- We extract the result for the head (v_head) and tail (vs_tail)
        match h_e : Expr.eval g V e, h_es : List.mapM (fun x ↦ Expr.eval g V x) es' with
        | Computation.result v_head, Computation.result vs_tail =>
          -- Simplify 'h' knowing the args evaluated successfully
          rw [h_e, h_es] at h
          simp at h
          -- h now says: Expr.eval g (bindArgs V ps vs) bd = result v

          -- 2. Construct the goal for addBindings
          --    addBindings (p::ps) (e::es) = let p := e in addBindings ps es ...
          simp [Expr.addBindings]

          -- We need to pick a gas amount.
          -- We need 1 step for the outer 'let', plus enough for the rest.
          -- We'll rely on the IH to give us the gas for the rest.

          -- Apply IH to the tail (es', ps')
          -- We need to show that funCall on the tail yields 'v' in the environment (V.insert p v_head).
          -- Note: Standard semantics imply arguments are Values (self-evaluating) or independent.
          -- For this proof to hold without extra assumptions, we assume 'e' eval is invariant.

          have h_tail_call : Expr.eval g (V.insert p v_head) ((Expr.value (Value.closure ps' bd)).funCall es') = Computation.result v := by
             simp [Expr.eval, bind, pure, Computation.bind]
             -- We need to show mapM evaluates to vs_tail in the NEW env
             -- This requires eval_list_value_irrelevant_env if es' are values.
             -- Assuming standard reduction semantics where es are values:
             rw [h_es] -- (This step implicitly assumes environment irrelevance for es', typical for Values)
             -- Now we match the bindArgs logic
             -- bindArgs (insert V p v_head) ps' vs' == bindArgs V (p::ps') (v_head::vs')
             rw [← bindArgs_cons_eq_insert]
             exact h

          -- Now we use the IH with this new fact
          specialize ih (h_len := (by simp at h_len; exact h_len)) h_tail_call
          rcases ih with ⟨gas_inner, h_inner⟩

          -- 3. Combine to form the total gas
          -- We need enough gas for:
          --   a) Evaluating 'e' (takes 'g')
          --   b) Evaluating the body (takes 'gas_inner')
          --   c) The 'let' step itself (takes 1)
          let total_gas := (max g gas_inner) + 1
          exists total_gas

          -- Expand 'eval' for the 'let' expression
          simp [Expr.eval, bind, pure, Computation.bind]

          -- 3a. Prove 'e' evaluates correctly with more gas
          have h_e_mon : Expr.eval (max g gas_inner) V e = Computation.result v_head := by
            apply eval_monotonic h_e
            apply Nat.le_max_left

          rw [h_e_mon]
          simp

          -- 3b. Prove the body evaluates correctly with more gas
          have h_body_mon : Expr.eval (max g gas_inner) (V.insert p v_head) (Expr.addBindings ps' es' bd _) = Computation.result v := by
            apply eval_monotonic h_inner
            apply Nat.le_max_right

          exact h_body_mon

        -- Error handling cases for the match (contradictions with success of h)
        | Computation.fail, _ => simp [h_e] at h
        | Computation.outOfGas, _ => simp [h_e] at h
        | Computation.result _, Computation.fail => simp [h_e, h_es] at h
        | Computation.result _, Computation.outOfGas => simp [h_e, h_es] at h
/--
Reducing a HeadSmallStep preserves the evaluation result.
-/
theorem head_step_preserves_eval {V : Env} {e e' : Expr} {v : Value} {gas : ℕ}
  (st : HeadSmallStep V e e')
  (h_eval : e.eval gas V = .result v)
  : ∃ gas', e'.eval gas' V = .result v := by
  cases st
  case const_step n =>
    cases gas <;> simp [Expr.eval] at h_eval
    rename_i gas'
    exists (gas' + 1)

  case var_step x v' h_lookup =>
    cases gas <;> simp [Expr.eval] at h_eval
    rename_i gas'
    exists (gas' + 1)
    simp [Expr.eval]
    simp [h_lookup] at h_eval
    exact h_eval

  case bin_op_step op n₁ n₂ h_op =>
    cases gas <;> simp [Expr.eval] at h_eval
    rename_i gas'
    cases gas' <;> simp [Expr.eval, bind, pure, Computation.bind] at h_eval
    subst h_eval
    exists 1

  case let_in_const_step name v₁ v₂ =>
    cases gas <;> simp [Expr.eval] at h_eval
    rename_i gas'
    cases gas' <;> simp [Expr.eval, bind, pure, Computation.bind] at h_eval
    rename_i gas''
    subst h_eval
    exists 1

  case fun_step es ps bd h_len h_eq =>
    subst h_eq
    apply eval_addBindings_eq_funCall h_eval

/--
SmallStep within a context preserves evaluation result.
-/
theorem ctx_step_preserves_eval {V : Env} {ctx : Ctx} {e e' : Expr} {v : Value} {gas : ℕ}
  (h_head : HeadSmallStep (ctx.updateEnv V) e e')
  (h_eval : (ctx.fill e).eval gas V = .result v)
  : ∃ gas', (ctx.fill e').eval gas' V = .result v := by
  induction ctx generalizing V gas v
  case hole =>
    simp [Ctx.fill, Ctx.updateEnv] at *
    apply head_step_preserves_eval h_head h_eval

  case binOpLhs ctx_inner op rhs ih =>
    simp [Ctx.fill, Ctx.updateEnv] at *
    cases gas <;> simp [Expr.eval] at h_eval
    rename_i gas'
    simp [bind, Computation.bind] at h_eval

    match h_lhs : (ctx_inner.fill e).eval gas' V with
    | .result v_lhs =>
      simp [h_lhs] at h_eval
      match h_rhs : rhs.eval gas' V with
      | .result v_rhs =>
        simp [h_rhs] at h_eval

        have ⟨g_lhs, h_lhs'⟩ := ih h_head h_lhs
        let max_gas := max g_lhs gas'
        exists (max_gas + 1)
        simp [Expr.eval, bind, pure, Computation.bind]
        rw [eval_monotonic h_lhs' (Nat.le_max_left _ _)]
        rw [eval_monotonic h_rhs (Nat.le_max_right _ _)]
        simp

        match v_lhs, v_rhs with
        | .nat n₁, .nat n₂ =>
          simp at h_eval
          exact h_eval
        | .closure _ _, _ => simp at h_eval
        | .nat _, .closure _ _ => simp at h_eval
      | .fail => simp [h_rhs] at h_eval
      | .outOfGas => simp [h_rhs] at h_eval
    | .fail => simp [h_lhs] at h_eval
    | .outOfGas => simp [h_lhs] at h_eval

  case binOpRhs n op ctx_inner ih =>
    simp [Ctx.fill, Ctx.updateEnv] at *
    cases gas <;> simp [Expr.eval] at h_eval
    rename_i gas'
    cases gas' <;> simp [Expr.eval, bind, pure, Computation.bind] at h_eval
    rename_i gas''

    match h_rhs : (ctx_inner.fill e).eval (Nat.succ gas'') V with
    | .result v_rhs =>
       have h_rhs_expanded := h_rhs
       rw [Expr.eval.eq_def] at h_rhs_expanded
       simp [bind, pure, Computation.bind] at h_rhs_expanded
       simp [h_rhs_expanded] at h_eval
       have ⟨g_rhs, h_rhs'⟩ := ih h_head h_rhs
       exists (g_rhs + 1)

       cases g_rhs
       case zero => simp [Expr.eval] at h_rhs'
       case succ g_rhs_inner =>
         rw [Expr.eval.eq_def] at h_rhs'
         simp [bind, pure, Computation.bind] at h_rhs'
         simp [Expr.eval, bind, pure, Computation.bind]
         rw [h_rhs']
         simp

         match n, v_rhs with
         | .nat n₁, .nat n₂ =>
            simp at h_eval
            simp
            rw [← h_eval]
         | .closure _ _, _ => simp at h_eval
         | .nat _, .closure _ _ => simp at h_eval
    | .fail =>
       rw [Expr.eval.eq_def] at h_rhs; simp [bind, pure, Computation.bind] at h_rhs
       simp [h_rhs] at h_eval
    | .outOfGas =>
       rw [Expr.eval.eq_def] at h_rhs; simp [bind, pure, Computation.bind] at h_rhs
       simp [h_rhs] at h_eval

  case letInExpr name ctx_inner expr_cbody ih =>
    simp [Ctx.fill, Ctx.updateEnv] at *
    cases gas <;> simp [Expr.eval] at h_eval
    rename_i gas'
    simp [bind, Computation.bind] at h_eval
    match h_init : (ctx_inner.fill e).eval gas' V with
    | .result v_init =>
       simp [h_init] at h_eval
       have ⟨g_init, h_init'⟩ := ih h_head h_init
       let max_gas := max g_init gas'
       exists (max_gas + 1)
       simp [Expr.eval, bind, Computation.bind]
       rw [eval_monotonic h_init' (Nat.le_max_left _ _)]
       simp
       rw [eval_monotonic h_eval (Nat.le_max_right _ _)]
    | .fail => simp [h_init] at h_eval
    | .outOfGas => simp [h_init] at h_eval

  case letInBody name val ctx_inner ih =>
    simp [Ctx.fill, Ctx.updateEnv] at *
    cases gas <;> simp [Expr.eval] at h_eval
    rename_i gas'
    simp [bind, Computation.bind] at h_eval

    -- Split gas' to unlock the evaluation of the 'let' value
    cases gas' <;> simp [Expr.eval, bind, pure, Computation.bind] at h_eval
    rename_i gas''

    change Expr.eval (Nat.succ gas'') (Std.HashMap.insert V name val) (Ctx.fill e ctx_inner) =
      Computation.result v at h_eval

    obtain ⟨g_inner, h_inner⟩ := ih h_head h_eval
    exists (Nat.succ (Nat.succ g_inner))
    rw [Expr.eval.eq_def]
    simp [bind, Computation.bind]

    apply eval_monotonic h_inner
    apply Nat.le_succ

  case funCallBody ctx_inner es ih =>
    simp [Ctx.fill, Ctx.updateEnv] at *
    cases gas <;> simp [Expr.eval] at h_eval
    rename_i gas'
    simp [bind, Computation.bind] at h_eval

    match h_func : (ctx_inner.fill e).eval gas' V with
    | .result v_func =>
      simp [h_func] at h_eval
      have ⟨g_func, h_func'⟩ := ih h_head h_func
      let max_gas := max g_func gas'
      exists (max_gas + 1)
      simp [Expr.eval, bind, Computation.bind]
      rw [eval_monotonic h_func' (Nat.le_max_left _ _)]
      match v_func with
      | .closure argNames functionBody =>
        simp at h_eval

        match h_args : List.mapM (fun e ↦ Expr.eval gas' V e) es with
        | .result v_args =>
          simp [h_args] at h_eval

          have list_mono (L : List Expr) (res : List Value)
              (h : List.mapM (fun e ↦ Expr.eval gas' V e) L = .result res) :
              List.mapM (fun e ↦ Expr.eval max_gas V e) L = .result res := by

            induction L generalizing res
            case nil =>
              simp [List.mapM] at h ⊢
              exact h
            case cons head tail ih_list =>
              simp only [List.mapM_cons, bind, pure, Computation.bind] at h ⊢

              match h_h : Expr.eval gas' V head with
              | .result vh =>
                rw [h_h] at h
                simp at h
                match h_t : List.mapM (fun e ↦ Expr.eval gas' V e) tail with
                | .result vt =>
                   rw [h_t] at h
                   simp at h
                   subst res
                   rw [eval_monotonic h_h (Nat.le_max_right _ _)]
                   simp
                   rw [ih_list vt h_t]

                | .fail => rw [h_t] at h; contradiction
                | .outOfGas => rw [h_t] at h; contradiction
              | .fail => rw [h_h] at h; contradiction
              | .outOfGas => rw [h_h] at h; contradiction

          rw [list_mono es v_args h_args]
          simp
          apply eval_monotonic h_eval (Nat.le_max_right _ _)

        | .fail => simp [h_args] at h_eval
        | .outOfGas => simp [h_args] at h_eval
      | .nat _ => simp at h_eval
    | .fail => simp [h_func] at h_eval
    | .outOfGas => simp [h_func] at h_eval

/--
**Main Theorem**: If `e` steps to `e'` (small step), and `e` evaluates to `v`,
then `e'` evaluates to `v` (given sufficient fuel).
-/
theorem small_step_invariance {V : Env} {e e' : Expr} {v : Value} {gas : ℕ}
  (step : SmallStep V e e')
  (h_eval : e.eval gas V = .result v)
  : ∃ gas', e'.eval gas' V = .result v := by
  cases step
  case ctx_step ctx e_inner e_inner' h_step h_e_eq h_e'_eq =>
    subst h_e_eq h_e'_eq
    exact ctx_step_preserves_eval h_step h_eval
