import LocalLang.AST
import LocalLang.DelayMonad
import Mathlib.Control.Traversable.Basic

def BinOp.eval : BinOp → ℕ → ℕ → ℕ
  | add, x, y => x + y
  | mul, x, y => x * y

def Func.updateEnv (func : Func) (V : Env) (args : List ℕ) : Env :=
  let param_arg_list := List.zip func.parameters args
  V ∪ .ofList param_arg_list

lemma list_all_some_of_sequence_some (os : List (Option N)) (ns : List N)
  (seq_some : sequence os = some ns) : os = .some <$> ns := by
  induction os generalizing ns with
  | nil =>
    simp only [sequence, traverse, List.traverse, Functor.map] at *
    injection seq_some with ns_eq
    simp [ns_eq]
  | cons o os' ih =>
    cases ns with
    | nil =>
      cases o with
      | none => simp [sequence, traverse, List.traverse, Seq.seq] at seq_some
      | some v => simp [sequence, traverse, List.traverse, Seq.seq, Functor.map] at *
    | cons n ns' =>
      cases o with
      | none => simp [sequence, traverse, List.traverse, Seq.seq] at seq_some
      | some val =>
        simp [sequence, traverse, List.traverse, Seq.seq, Functor.map] at *
        let ⟨traverse_eq, val_eq⟩ := seq_some
        constructor
        · assumption
        · exact ih ns' traverse_eq

lemma sequence_of_some_eq_original {xs : List ℕ} : sequence (some <$> xs) = xs := by
  induction xs with
  | nil => simp [Functor.map, sequence, traverse, List.traverse]
  | cons x xs' ih =>
    simp [sequence, traverse, List.traverse, Seq.seq, Functor.map] at *
    assumption

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
    let V_with_args := func.updateEnv V args
    func.body.eval V_with_args D
  | letIn x e body => do
    let vₓ <- e.eval V D
    body.eval (V.insert x vₓ) D

def Expr.evalFinite (V : Env) (D : Definitions) (n : ℕ) : Expr → Option ℕ
  | const k => k
  | var x => V[x]?
  | binOp op e₁ e₂ => match n with
    | .zero => none
    | .succ n' => do
      let v₁ <- e₁.evalFinite V D n'
      let v₂ <- e₂.evalFinite V D n'
      pure (op.eval v₁ v₂)
  | funCall f es => match n with
    | .zero => none
    | .succ n' => do
      let func <- D[f]?
      let args_opt : List (Option ℕ) := es.map (·.evalFinite V D n')
      let args : List ℕ <- sequence args_opt
      let V_with_args := func.updateEnv V args
      func.body.evalFinite V_with_args D n'
  | letIn x e body => match n with
    | .zero => none
    | .succ n' => do
      let vₓ <- e.evalFinite V D n'
      body.evalFinite (V.insert x vₓ) D n'

def Expr.eval' (V : Env) (D : Definitions) (e : Expr) : DelayM ℕ := ⟨
  fun n => e.evalFinite V D n,
  by
    intro n a some_h
    beta_reduce at *
    induction n generalizing e a V <;> cases e <;> simp only [evalFinite] at * <;>
      try first | assumption | contradiction
    case succ.binOp n' ih op e₁ e₂ => (
      cases e₁_eval_n' : e₁.evalFinite V D n' <;> try simp [e₁_eval_n'] at some_h
      cases e₂_eval_n' : e₂.evalFinite V D n' <;> try simp [e₂_eval_n'] at some_h
      rename_i lhs_val rhs_val
      let e₁_eval_n := ih _ e₁ _ e₁_eval_n'
      let e₂_eval_n := ih _ e₂ _ e₂_eval_n'
      rw [e₁_eval_n, e₂_eval_n, ← some_h]
      simp
    )
    case succ.letIn n' ih x e body => (
      cases e_eval_n' : evalFinite V D n' e <;> try simp [e_eval_n'] at some_h
      let e_eval_n := ih _ e _ e_eval_n'
      let body_eval_n := ih _ body _ some_h
      simp [e_eval_n, body_eval_n]
    )
    case succ.funCall n' ih f es => (
      cases f_in : D[f]? <;> try simp [f_in] at some_h
      cases args_eval_n' : sequence (es.map (·.evalFinite V D n'))
        <;> try simp [args_eval_n'] at some_h
      rename_i func es_vals
      let eval_n'_eq_es_vals := list_all_some_of_sequence_some _ es_vals args_eval_n'
      let eval_n_eq_es_vals : es.map (·.evalFinite V D (n' + 1)) = some <$> es_vals := by sorry
      simp [eval_n_eq_es_vals, sequence_of_some_eq_original]
      apply ih
      assumption
    )
⟩

def evaluate (prog : Program) : DelayM ℕ := prog.main.eval' ∅ prog.definitions
