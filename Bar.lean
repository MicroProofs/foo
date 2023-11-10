
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
  | compute (m: Term) (ρ : List (String × Value)) (s : Stack) : State
  | ret (v: Value) (s : Stack) : State
  | error : State
  | halt (v: Value) : State
deriving Repr


def lookup_var (e: List (String × Value)) (x: String) : Option Value :=
  match e with
  | []  => none
  | (y, v) :: e => if x == y then some v else lookup_var e x

inductive small_step : State -> State -> Prop
  | seq {s s' s''} (h: small_step s s') (h': small_step s' s''):
    small_step s s''
  | computeLookup {x p s} (h: lookup_var p x = some v): small_step (State.compute (Term.var x) p s) (State.ret v s)
  | computeConstant {c p s} : small_step (State.compute (Term.con c) p s) (State.ret (Value.vCon c) s)
  | computeLambda {x m p s} : small_step (State.compute (Term.lam x m) p s) (State.ret (Value.vLam x m p) s)
  | computeDelay {m p s} : small_step (State.compute (Term.delay m) p s) (State.ret (Value.vDelay m p) s)
  | computeForce {m p s} : small_step (State.compute (Term.force m) p s) (State.compute m p (Frame.force :: s))
  | computeApp {m n p s} : small_step (State.compute (Term.app m n) p s) (State.compute m p (Frame.leftAppTerm n p :: s))
  | computeBuiltin {b p s} : small_step (State.compute (Term.builtin b) p s) (State.ret (Value.vBuiltin (BuiltinValue.builtin b)) s)
  | computeError {p s} : small_step (State.compute Term.error p s) State.error
  | ret {v s} : small_step (State.ret v s) (State.halt v)
  | retLeftAppTerm {m p v s} : small_step (State.ret v (Frame.leftAppTerm m p :: s)) (State.compute m p (Frame.rightApp v :: s))
  | retRightApp {x m p v s} : small_step (State.ret v (Frame.rightApp (Value.vLam x m p) :: s)) (State.compute m ((x, v) :: p) s)
  | retLeftAppValue {x m p v s} : small_step (State.ret (Value.vLam x m p) (Frame.leftAppValue v :: s)) (State.compute m ((x, v) :: p) s)
  | retRightAppBuiltin {b v s} : small_step (State.ret v (Frame.rightApp (Value.vBuiltin b) :: s)) (State.ret (Value.vBuiltin (BuiltinValue.app b v)) s)
  | retLeftAppValueBuiltin {b v s} : small_step (State.ret (Value.vBuiltin b) (Frame.leftAppValue v :: s)) (State.ret (Value.vBuiltin (BuiltinValue.app b v)) s)
  | retDelay {m p s} : small_step (State.ret (Value.vDelay m p) (Frame.force :: s)) (State.compute m p s)
  | retBuiltin {b s} : small_step (State.ret (Value.vBuiltin b) (Frame.force :: s)) (State.ret (Value.vBuiltin (BuiltinValue.force b)) s)
  | catchAll {s} : small_step s State.error

  -- inductive small_step : (Instruction × State) -> (Instruction × State) -> Prop
  -- | seq {m m' m'' s s' s''} (h: small_step (m, s) (m', s')) (h': small_step (m', s') (m'', s'')):
  --   small_step (m, s) (m'', s'')

  -- | computeLookup {v x p s} (h: lookup_var p x = some v):
  --   small_step (Instruction.term (Term.var x), State.compute p s) (Instruction.value v, State.ret s)

  -- | computeConstant {c p s} : small_step (Instruction.term (Term.con c) ,State.compute p s) (Instruction.value (Value.vCon c), State.ret s)
  -- | computeLambda {x m p s} : small_step (Instruction.term (Term.lam x m), State.compute p s) (Instruction.value (Value.vLam x m p), State.ret s)
  -- | computeDelay {m p s} : small_step (Instruction.term (Term.delay m), State.compute p s) (Instruction.value (Value.vDelay m p), State.ret s)
  -- | computeForce {m p s} : small_step (Instruction.term (Term.force m), State.compute p s) (Instruction.term m, State.compute p (Frame.force :: s))
  -- | computeApp {m n p s} : small_step (Instruction.term (Term.app m n), State.compute p s) (Instruction.term m, State.compute p (Frame.leftAppTerm n p :: s))
  -- | computeBuiltin {b p s} : small_step (Instruction.term (Term.builtin b), State.compute  p s) (Instruction.value (Value.vBuiltin (BuiltinValue.builtin b)), State.ret s)
  -- | computeError {p s} : small_step (Instruction.term Term.error, State.compute p s) (Instruction.term Term.error, State.error)
  -- | ret {v} : small_step (Instruction.value v, State.ret []) (Instruction.value v, State.halt)
  -- | retLeftAppTerm {m p v s} : small_step (Instruction.value v, State.ret (Frame.leftAppTerm m p :: s)) (Instruction.term m, State.compute p (Frame.rightApp v :: s))
  -- | retRightApp {x m p v s} : small_step (Instruction.value v, State.ret (Frame.rightApp (Value.vLam x m p) :: s)) (Instruction.term m, State.compute ((x, v) :: p) s)
  -- | retLeftAppValue {x m p v s} : small_step (Instruction.value (Value.vLam x m p), State.ret (Frame.leftAppValue v :: s)) (Instruction.term m, State.compute ((x, v) :: p) s)
  -- | retRightAppBuiltin {b v s} : small_step (Instruction.value v, State.ret (Frame.rightApp (Value.vBuiltin b) :: s)) (Instruction.value (Value.vBuiltin (BuiltinValue.app b v)), State.ret s)
  -- | retLeftAppValueBuiltin {b v s} : small_step (Instruction.value (Value.vBuiltin b), State.ret  (Frame.leftAppValue v :: s)) (Instruction.value (Value.vBuiltin (BuiltinValue.app b v)), State.ret s)
  -- -- TODO: Eval builtins
  -- | retDelay {m p s} : small_step (Instruction.value (Value.vDelay m p), State.ret (Frame.force :: s)) (Instruction.term m, State.compute p s)
  -- | retBuiltin {b s} : small_step (Instruction.value (Value.vBuiltin b), State.ret (Frame.force :: s)) (Instruction.value (Value.vBuiltin (BuiltinValue.force b)), State.ret s)
  -- | catchAll {m s} : small_step (m, s) ((Instruction.term Term.error), State.error)


infix: 90 "⟶" => small_step



theorem small_step_compute_lambda
{x m p s} : (State.compute (Term.lam x m) p s) ⟶ (State.ret (Value.vLam x m p) s) := by
  apply small_step.computeLambda


theorem frame_force_delay_just_term
  {m p s}:
  (State.compute (Term.delay m) p (Frame.force :: s)) ⟶
  (State.compute m p s) := by
    have h': (State.compute (Term.delay m) p (Frame.force :: s)) ⟶
      (State.ret (Value.vDelay m p) (Frame.force :: s)) := by
        apply small_step.computeDelay
    have h'': (State.ret (Value.vDelay m p) (Frame.force :: s)) ⟶
      (State.compute m p s) := by
        apply small_step.retDelay
    exact small_step.seq h' h''

theorem forcing
  {m p s}:
  (State.compute (Term.force (Term.force m)) p (s)) ⟶
  (State.compute m p (Frame.force :: Frame.force :: s)) := by
    exact small_step.seq small_step.computeForce small_step.computeForce


theorem force_delay_just_term
  {m p s}:
  (State.compute (Term.force (Term.delay m)) p s) ⟶
  (State.compute m p s) := by
    have h: (State.compute (Term.force (Term.delay m)) p s) ⟶
      (State.compute (Term.delay m) p (Frame.force :: s)) := by
        apply small_step.computeForce
    have h': (State.compute (Term.delay m) p (Frame.force :: s)) ⟶
      (State.ret (Value.vDelay m p) (Frame.force :: s)) := by
        apply small_step.computeDelay
    have h'': (State.ret (Value.vDelay m p) (Frame.force :: s)) ⟶
      (State.compute m p s) := by
        apply small_step.retDelay
    exact small_step.seq (small_step.seq h h') h''

theorem double_force_term
  {m p s}:
  (State.compute (Term.force (Term.force m)) p s) ⟶
  (State.compute m p (Frame.force :: Frame.force :: s)) := by
    have h: (State.compute (Term.force (Term.force m)) p s) ⟶
      (State.compute (Term.force m) p (Frame.force :: s)) := by
        apply small_step.computeForce
    let s' := Frame.force :: s
    have h': (State.compute (Term.force m) p s') ⟶
      (State.compute m p (Frame.force :: s')) := by
        apply small_step.computeForce
    exact small_step.seq h h'

theorem force_delay_term
  {m p s}:
  (State.compute (Term.force (Term.force (Term.delay (Term.delay m)))) p s) ⟶
  (State.compute m p s) := by
    have h: (State.compute (Term.force (Term.force (Term.delay (Term.delay m)))) p s) ⟶
      (State.compute (Term.force (Term.delay (Term.delay m))) p (Frame.force :: s)) := by
        apply small_step.computeForce
    have h': (State.compute (Term.force (Term.delay (Term.delay m))) p (Frame.force :: s)) ⟶
      (State.compute (Term.delay m) p (Frame.force :: s)) := by
        exact force_delay_just_term
    have h'': (State.compute (Term.delay m) p (Frame.force :: s)) ⟶
      (State.compute m p s) := by
        apply frame_force_delay_just_term
    exact small_step.seq (small_step.seq h h') h''

theorem forces
  {m p s}:
  (State.compute (Term.force (Term.force (Term.force (Term.delay (Term.delay (Term.delay m)))))) p s) ⟶
  (State.compute m p s) := by
    apply small_step.seq
    case h =>
      apply small_step.seq
      case h => exact forcing
      case h' => exact force_delay_just_term
    case h' =>
      apply small_step.seq
      case h => exact frame_force_delay_just_term
      case h' => exact frame_force_delay_just_term

theorem forces2
  {m p s}:
  (State.compute (Term.force (Term.force (Term.force (Term.delay (Term.delay (Term.delay m)))))) p s) ⟶
  (State.compute m p s) := by
    repeat (
      first
      | apply forcing
      | apply force_delay_just_term
      | apply frame_force_delay_just_term
      | apply small_step.seq
    )


theorem forces3
  {m p s}:
  (State.compute (Term.force (Term.force (Term.force (Term.delay (Term.delay (Term.delay m)))))) p s) ⟶
  (State.compute m p s) := by
    repeat (first | apply small_step.computeForce | apply small_step.computeDelay | apply small_step.retDelay | apply small_step.seq)



theorem lam_apply_var_is_applied_term
  {x p}:
  (State.compute (Term.app (Term.lam x (Term.var x)) (Term.con 5)) p []) ⟶
  (State.halt (Value.vCon 5)) := by
    apply small_step.seq
    case h => exact small_step.computeApp
    case h' =>
      apply small_step.seq
      case h => exact small_step.computeLambda
      case h' =>
        apply small_step.seq
        case h => exact small_step.retLeftAppTerm
        case h' =>
          apply small_step.seq
          case h => exact small_step.computeConstant
          case h' =>
            apply small_step.seq
            case h => exact small_step.retRightApp
            case h' =>
              apply small_step.seq
              case h =>
                apply small_step.computeLookup;
                case h =>
                  rw [lookup_var]
                  simp
                  rfl
              case h' => exact small_step.ret






theorem lam_apply_var_is_applied_term2
  {x p}:
  (State.compute (Term.app (Term.lam x (Term.var x)) (Term.con 5)) p []) ⟶
  (State.halt (Value.vCon 5)) := by
    repeat (first | apply small_step.computeApp | apply small_step.computeLambda | apply small_step.retLeftAppTerm | apply small_step.computeConstant | apply small_step.retRightApp | apply small_step.computeLookup | apply small_step.ret | apply small_step.seq)
