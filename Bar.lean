
def hello := "world"
open String
open Nat
open Int
open List

structure Builtin where
  function: Nat
deriving Repr

inductive Term where
  | var (x : String) : Term
  | builtin (b: Builtin): Term
  | con (c : Int) : Term
  | lam (x: String) (m : Term) : Term
  | app (m : Term) (n : Term) : Term
  | delay (m : Term) : Term
  | force (m : Term) : Term
  | error : Term
deriving Repr

structure Program where
 v: Nat
 m: Term
deriving Repr

mutual
inductive Value where
  | vCon (c : Int) : Value
  | vLam (x: String) (m : Term) (p: List (String × Value)) : Value
  | vDelay (m : Term) (p: List (String × Value)) : Value
  | vBuiltin (b: BuiltinValue): Value
deriving Repr

inductive BuiltinValue where
  | builtin (b: Builtin): BuiltinValue
  | app (b: BuiltinValue) (v: Value): BuiltinValue
  | force (b: BuiltinValue): BuiltinValue
deriving Repr
end

inductive Frame where
  | force : Frame
  | leftAppTerm (m : Term) (p : List (String × Value)) : Frame
  | leftAppValue (v : Value) : Frame
  | rightApp (v : Value) : Frame
deriving Repr


def Stack := List Frame
deriving Repr

inductive State where
  | compute (ρ : List (String × Value)) (s : Stack) : State
  | ret (s : Stack) : State
  | error : State
  | halt : State
deriving Repr

inductive Instruction where
  | term (t: Term): Instruction
  | value (v: Value): Instruction

def lookup_var (e: List (String × Value)) (x: String) : Option Value :=
  match e with
  | []  => none
  | (y, v) :: e => if x == y then some v else lookup_var e x

-- inductive big_step : State -> State -> Prop
--   | computeLookup {x p s} :
--     big_step (State.compute (Term.var x) p s) (match lookup_var p x with | none => State.error | some v => State.ret v s)
--   | computeConstant {c p s} : big_step (State.compute (Term.con c) p s) (State.ret (Value.vCon c) s)
--   | computeLambda {x m p s} : big_step (State.compute (Term.lam x m) p s) (State.ret (Value.vLam x m p) s)
--   | computeDelay {m p s} : big_step (State.compute (Term.delay m) p s) (State.ret (Value.vDelay m p) s)
--   | computeForce {m p s} : big_step (State.compute (Term.force m) p s) (State.compute m p (Frame.force :: s))
--   | computeApp {m n p s} : big_step (State.compute (Term.app m n) p s) (State.compute m p (Frame.leftAppTerm n p :: s))
--   | computeBuiltin {b p s} : big_step (State.compute (Term.builtin b) p s) (State.ret (Value.vBuiltin (BuiltinValue.builtin b)) s)
--   | computeError {p s} : big_step (State.compute Term.error p s) State.error
--   | ret {v s} : big_step (State.ret v s) (State.halt v)
--   | retLeftAppTerm {m p v s} : big_step (State.ret v (Frame.leftAppTerm m p :: s)) (State.compute m p (Frame.rightApp v :: s))
--   | retRightApp {x m p v s} : big_step (State.ret v (Frame.rightApp (Value.vLam x m p) :: s)) (State.compute m ((x, v) :: p) s)
--   | retLeftAppValue {x m p v s} : big_step (State.ret (Value.vLam x m p) (Frame.leftAppValue v :: s)) (State.compute m ((x, v) :: p) s)
--   | retRightAppBuiltin {b v s} : big_step (State.ret v (Frame.rightApp (Value.vBuiltin b) :: s)) (State.ret (Value.vBuiltin (BuiltinValue.app b v)) s)
--   | retLeftAppValueBuiltin {b v s} : big_step (State.ret (Value.vBuiltin b) (Frame.leftAppValue v :: s)) (State.ret (Value.vBuiltin (BuiltinValue.app b v)) s)
--   | retDelay {m p s} : big_step (State.ret (Value.vDelay m p) (Frame.force :: s)) (State.compute m p s)
--   | retBuiltin {b s} : big_step (State.ret (Value.vBuiltin b) (Frame.force :: s)) (State.ret (Value.vBuiltin (BuiltinValue.force b)) s)
--   | catchAll {s} : big_step s State.error

  inductive small_step : (Instruction × State) -> (Instruction × State) -> Prop
  | seq {m m' m'' s s' s''} (h: small_step (m, s) (m', s')) (h': small_step (m', s') (m'', s'')):
    small_step (m, s) (m'', s'')

  | computeLookup {v x p s} :
    small_step (Instruction.term (Term.var x), State.compute ((x, v) :: p) s) (Instruction.value v, State.ret s)

  | computeConstant {c p s} : small_step (Instruction.term (Term.con c) ,State.compute p s) (Instruction.value (Value.vCon c), State.ret s)
  | computeLambda {x m p s} : small_step (Instruction.term (Term.lam x m), State.compute p s) (Instruction.value (Value.vLam x m p), State.ret s)
  | computeDelay {m p s} : small_step (Instruction.term (Term.delay m), State.compute p s) (Instruction.value (Value.vDelay m p), State.ret s)
  | computeForce {m p s} : small_step (Instruction.term (Term.force m), State.compute p s) (Instruction.term m, State.compute p (Frame.force :: s))
  | computeApp {m n p s} : small_step (Instruction.term (Term.app m n), State.compute p s) (Instruction.term m, State.compute p (Frame.leftAppTerm n p :: s))
  | computeBuiltin {b p s} : small_step (Instruction.term (Term.builtin b), State.compute  p s) (Instruction.value (Value.vBuiltin (BuiltinValue.builtin b)), State.ret s)
  | computeError {p s} : small_step (Instruction.term Term.error, State.compute p s) (Instruction.term Term.error, State.error)
  | ret {v} : small_step (Instruction.value v, State.ret []) (Instruction.value v, State.halt)
  | retLeftAppTerm {m p v s} : small_step (Instruction.value v, State.ret (Frame.leftAppTerm m p :: s)) (Instruction.term m, State.compute p (Frame.rightApp v :: s))
  | retRightApp {x m p v s} : small_step (Instruction.value v, State.ret (Frame.rightApp (Value.vLam x m p) :: s)) (Instruction.term m, State.compute ((x, v) :: p) s)
  | retLeftAppValue {x m p v s} : small_step (Instruction.value (Value.vLam x m p), State.ret (Frame.leftAppValue v :: s)) (Instruction.term m, State.compute ((x, v) :: p) s)
  | retRightAppBuiltin {b v s} : small_step (Instruction.value v, State.ret (Frame.rightApp (Value.vBuiltin b) :: s)) (Instruction.value (Value.vBuiltin (BuiltinValue.app b v)), State.ret s)
  | retLeftAppValueBuiltin {b v s} : small_step (Instruction.value (Value.vBuiltin b), State.ret  (Frame.leftAppValue v :: s)) (Instruction.value (Value.vBuiltin (BuiltinValue.app b v)), State.ret s)
  -- TODO: Eval builtins
  | retDelay {m p s} : small_step (Instruction.value (Value.vDelay m p), State.ret (Frame.force :: s)) (Instruction.term m, State.compute p s)
  | retBuiltin {b s} : small_step (Instruction.value (Value.vBuiltin b), State.ret (Frame.force :: s)) (Instruction.value (Value.vBuiltin (BuiltinValue.force b)), State.ret s)
  | catchAll {m s} : small_step (m, s) ((Instruction.term Term.error), State.error)


infix: 90 "⟶" => small_step



theorem small_step_compute_lambda
{x m p s} : (Instruction.term (Term.lam x m), State.compute  p s) ⟶ (Instruction.value (Value.vLam x m p), State.ret s) := by
  apply small_step.computeLambda


theorem force_delay_just_term
  {m p s}:
  (Instruction.term (Term.force (Term.delay m)), State.compute p s) ⟶
  (Instruction.term m, State.compute p s) := by
    have h: (Instruction.term (Term.force (Term.delay m)), State.compute p s) ⟶
      (Instruction.term (Term.delay m), State.compute p (Frame.force :: s)) := by
        apply small_step.computeForce
    have h': (Instruction.term (Term.delay m), State.compute p (Frame.force :: s)) ⟶
      (Instruction.value (Value.vDelay m p), State.ret (Frame.force :: s)) := by
        apply small_step.computeDelay
    have h'': (Instruction.value (Value.vDelay m p), State.ret (Frame.force :: s)) ⟶
      (Instruction.term m, State.compute p s) := by
        apply small_step.retDelay
    exact small_step.seq (small_step.seq h h') h''



theorem lam_apply_var_is_applied_term
  {x p s}:
  (Instruction.term (Term.app (Term.lam x (Term.var x)) (Term.con 5)), State.compute p s) ⟶
  (Instruction.value (Value.vCon 5), State.ret s) := by
    have h: (Instruction.term (Term.app (Term.lam x (Term.var x)) (Term.con 5)), State.compute p s) ⟶
      (Instruction.term (Term.lam x (Term.var x)), State.compute p (Frame.leftAppTerm (Term.con 5) p :: s)) := by
        apply small_step.computeApp
    have h': (Instruction.term (Term.lam x (Term.var x)), State.compute p (Frame.leftAppTerm (Term.con 5) p :: s)) ⟶
      (Instruction.value (Value.vLam x (Term.var x) p), State.ret (Frame.leftAppTerm (Term.con 5) p :: s)) := by
        apply small_step.computeLambda
    have h'': (Instruction.value (Value.vLam x (Term.var x) p), State.ret (Frame.leftAppTerm (Term.con 5) p :: s)) ⟶
      (Instruction.term (Term.con 5), State.compute p ((Frame.rightApp (Value.vLam x (Term.var x) p)) :: s)) := by
        apply small_step.retLeftAppTerm
    have h''': (Instruction.term (Term.con 5), State.compute p ((Frame.rightApp (Value.vLam x (Term.var x) p)) :: s)) ⟶
      (Instruction.value (Value.vCon 5), State.ret ((Frame.rightApp (Value.vLam x (Term.var x) p)) :: s)) := by
        apply small_step.computeConstant
    have h'''': (Instruction.value (Value.vCon 5), State.ret ((Frame.rightApp (Value.vLam x (Term.var x) p)) :: s)) ⟶
      (Instruction.term (Term.var x), State.compute ((x, (Value.vCon 5)) :: p) s) := by
        apply small_step.retRightApp
    have h''''' : (Instruction.term (Term.var x), State.compute ((x, (Value.vCon 5)) :: p) s) ⟶
      (Instruction.value (Value.vCon 5), State.ret s) := by
        apply small_step.computeLookup
    exact small_step.seq (small_step.seq (small_step.seq (small_step.seq (small_step.seq h h') h'') h''') h'''') h'''''



-- partial def reduc (st : State) : State :=
--   match st with
--   | State.compute (Term.var x) ρ s => match lookup_var ρ x with
--     | none => State.error
--     | some v => reduc (State.ret v s)
--   | State.compute (Term.con c) _ s => reduc (State.ret (Value.vCon c) s)
--   | State.compute (Term.lam x m) ρ s => reduc (State.ret (Value.vLam x m ρ) s)
--   | State.compute (Term.delay m) ρ s => reduc (State.ret (Value.vDelay m ρ) s)
--   | State.compute (Term.force m) ρ s => reduc (State.compute m ρ (Frame.force :: s))
--   | State.compute (Term.app m n) p s => reduc (State.compute m p (Frame.leftAppTerm n p :: s))
--   | State.compute (Term.builtin b) _ s => reduc (State.ret (Value.vBuiltin (BuiltinValue.builtin b)) s)
--   | State.compute Term.error _ _ => State.error
--   | State.ret v [] => State.halt v
--   | State.ret v (Frame.leftAppTerm m p :: s) => reduc (State.compute m p (Frame.rightApp v :: s))
--   | State.ret v (Frame.rightApp (Value.vLam x m p) :: s) => reduc (State.compute m ((x, v) :: p) s)
--   | State.ret (Value.vLam x m p) (Frame.leftAppValue v :: s) => reduc (State.compute m ((x, v) :: p) s)
--   | State.ret v (Frame.rightApp (Value.vBuiltin b) :: s) => reduc (State.ret (Value.vBuiltin (BuiltinValue.app b v)) s)
--   | State.ret (Value.vBuiltin b) (Frame.leftAppValue v :: s) => reduc (State.ret (Value.vBuiltin (BuiltinValue.app b v)) s)
--   -- TODO: Eval builtins
--   | State.ret (Value.vDelay m p) (Frame.force :: s) => reduc (State.compute m p s)
--   | State.ret (Value.vBuiltin b) (Frame.force :: s) => reduc (State.ret (Value.vBuiltin (BuiltinValue.force b)) s)
--   | _ => State.error

-- def run (p: Program) : State :=
--   reduc (State.compute p.m [] [])

-- def test2 : State :=
--   let x := run ({v := 0, m := Term.app (Term.lam "so" (Term.var "so")) (Term.con 5)})
--   x


-- #eval test2
