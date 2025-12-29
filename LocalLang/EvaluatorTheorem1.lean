import LocalLang.AST
import LocalLang.Evaluator
import LocalLang.Semantics
import LocalLang.SemanticsLemmas
import LocalLang.Ctx
import LocalLang.EvaluatorTheorem3
import Std.Data.HashMap.Lemmas
import Std.Data.HashMap

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

lemma env_insert_commute (V : Env) (n1 n2 : String) (v1 v2 : Value) (h_neq : n1 ≠ n2) :
    Std.HashMap.insert (Std.HashMap.insert V n1 v1) n2 v2 =
    Std.HashMap.insert (Std.HashMap.insert V n2 v2) n1 v1 := by
  -- My environment doesn't pick up the necessary lemmas from Std.HashMap so I can't prove this :(
  sorry

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

      -- Reduce Left Hand Side
      conv =>
        lhs
        dsimp [Expr.eval]
        simp only [Expr.eval, bind, pure, Computation.bind]
        dsimp [Expr.eval]
        simp only [Expr.eval, bind, pure, Computation.bind]

      -- Reduce Right Hand Side
      conv =>
        rhs
        dsimp [Expr.eval]
        simp only [Expr.eval, bind, pure, Computation.bind]
        dsimp [Expr.eval]
        simp only [Expr.eval, bind, pure, Computation.bind]

      rw [env_insert_commute V n1 n2 v1 v2 h_neq]

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
  induction ps generalizing es bd V gas v
  case nil =>
    sorry

  case cons p ps' ih =>
    cases es
    case nil => contradiction
    case cons e es' =>
      -- Split gas once. funCall needs 1 step. let needs 1 step.
      cases gas
      case zero =>
        -- If gas is 0, funCall fails immediately. Contradiction with 'h'.
        simp [Expr.eval] at h

      case succ gas' =>
        sorry

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
