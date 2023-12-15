def hello := "world"
open String
open Nat
open Int
open List

-- Term and Program Structures
def Name := String
deriving Repr

inductive Function where
  | addInteger : Function
  | subtractInteger : Function
deriving Repr

structure Builtin where
  function: Function
deriving Repr

def builtin_arity (function: Function): Nat × Nat :=
  match function with
  | .addInteger => (0, 2)
  | .subtractInteger => (0, 2)

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

-- Value Structures
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

-- Partial Builtin functions
def builtin_name (b: BuiltinValue): Function :=
  match b with
    | .builtin b => b.function
    | .app b _ => builtin_name b
    | .force b => builtin_name b

def force_size (b: BuiltinValue): Nat :=
  match b with
    | .force b => (force_size b) + 1
    | .app b _ => (force_size b)
    | _ => 0

def builtin_args (b: BuiltinValue): List Value :=
  match b with
    | .builtin _ => []
    | .app b v => (builtin_args b) ++ [v]
    | .force _ => []

def builtin_size (b: BuiltinValue): Nat × Nat :=
  match b with
    | .builtin _ => (0, 0)
    | .app _ _ => (force_size b, List.length (builtin_args b))
    | .force _ => (force_size b, 0)

def not_all_args_applied (args: Nat × Nat) (arity: Nat × Nat): Prop :=
  let (forces, applies) := args
  let (forces_arity, apply_arity) := arity
  applies < apply_arity || forces < forces_arity


-- Term Reduction

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


def Environment := List (String × Value)

def lookup_var (e: Environment) (x: String): Option Value :=
  match e with
  | []  => none
  | (y, v) :: e => if x == y then some v else lookup_var e x


theorem args_length_is_size {b}: List.length (builtin_args b) = (builtin_size b).snd := by
  cases b with
  | builtin a =>
    rw [builtin_args, builtin_size]
    rfl
  | app a v =>
    rw [builtin_args, builtin_size]
    simp [builtin_args]
  | force a =>
    simp [builtin_args, builtin_size]

theorem args_length_is_arity {b} (h: builtin_size b = builtin_arity (builtin_name b)) :
  List.length (builtin_args b) = (builtin_arity (builtin_name b)).snd := by
    have h': List.length (builtin_args b) = (builtin_size b).snd := by
      apply args_length_is_size
    have h'': (builtin_arity (builtin_name b)).snd = (builtin_size b).snd := by
      simp [h]
    simp [h', h'']



def eval_builtin (s: Stack) (b: BuiltinValue) (h: builtin_size b = builtin_arity (builtin_name b)) : State :=
  let args := builtin_args b
  have j: 1 < List.length args := by
    simp [args_length_is_arity, h, builtin_arity]
    cases builtin_name b with
      | _ => simp

   have jj: 0 < List.length args := by
    simp [args_length_is_arity, h, builtin_arity]
    cases builtin_name b with
      | _ => simp

  match (builtin_name b) with
    | Function.addInteger => match (args[0]'jj, args[1]'j) with
      | (Value.vCon l, Value.vCon r) =>
        State.ret (Value.vCon (l + r)) s
      | (_, _) => State.error

    | Function.subtractInteger => match (args[0]'jj, args[1]'j) with
      | (Value.vCon l, Value.vCon r) =>
        State.ret (Value.vCon (l - r)) s
      | (_, _) => State.error





inductive small_step : State -> State -> Prop
  | seq {s s' s''} (h: small_step s s') (h': small_step s' s''): small_step s s''

  | computeLookup {x p s} (h: lookup_var p x = some v): small_step (State.compute (Term.var x) p s) (State.ret v s)

  | computeConstant {c p s} : small_step (State.compute (Term.con c) p s) (State.ret (Value.vCon c) s)

  | computeLambda {x m p s} : small_step (State.compute (Term.lam x m) p s) (State.ret (Value.vLam x m p) s)

  | computeDelay {m p s} : small_step (State.compute (Term.delay m) p s) (State.ret (Value.vDelay m p) s)

  | computeForce {m p s} : small_step (State.compute (Term.force m) p s) (State.compute m p (Frame.force :: s))

  | computeApp {m n p s} : small_step (State.compute (Term.app m n) p s) (State.compute m p (Frame.leftAppTerm n p :: s))

  | computeBuiltin {b p s} : small_step (State.compute (Term.builtin b) p s) (State.ret (Value.vBuiltin (BuiltinValue.builtin b)) s)

  | computeError {p s} : small_step (State.compute Term.error p s) State.error

  | ret {v} : small_step (State.ret v []) (State.halt v)

  | retLeftAppTerm {m p v s} : small_step (State.ret v (Frame.leftAppTerm m p :: s)) (State.compute m p (Frame.rightApp v :: s))

  | retRightApp {x m p v s} : small_step (State.ret v (Frame.rightApp (Value.vLam x m p) :: s)) (State.compute m ((x, v) :: p) s)

  | retLeftAppValue {x m p v s} : small_step (State.ret (Value.vLam x m p) (Frame.leftAppValue v :: s)) (State.compute m ((x, v) :: p) s)

  | retRightAppBuiltin {b v s} (h: not_all_args_applied (builtin_size b) (builtin_arity (builtin_name b))) : small_step (State.ret v (Frame.rightApp (Value.vBuiltin b) :: s)) (State.ret (Value.vBuiltin (BuiltinValue.app b v)) s)

  | retLeftAppValueBuiltin {b v s} (h: not_all_args_applied (builtin_size b) (builtin_arity (builtin_name b))) : small_step (State.ret (Value.vBuiltin b) (Frame.leftAppValue v :: s)) (State.ret (Value.vBuiltin (BuiltinValue.app b v)) s)

  | builtinEval {b s} (h: builtin_size b = builtin_arity (builtin_name b)) (h': eval_builtin s b h = s' ) : small_step (State.ret (Value.vBuiltin b) s) s'

  | retForceDelay {m p s} : small_step (State.ret (Value.vDelay m p) (Frame.force :: s)) (State.compute m p s)

  | retForceBuiltin {b s} : small_step (State.ret (Value.vBuiltin b) (Frame.force :: s)) (State.ret (Value.vBuiltin (BuiltinValue.force b)) s)

  | catchAll {s} : small_step s State.error


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
        apply small_step.retForceDelay
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
        apply small_step.retForceDelay
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
    repeat (first | apply small_step.computeForce | apply small_step.computeDelay | apply small_step.retForceDelay | apply small_step.seq)



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
                  simp [lookup_var]
                  rfl
              case h' => exact small_step.ret






theorem lam_apply_var_is_applied_term2
  {x p}:
  (State.compute (Term.app (Term.lam x (Term.var x)) (Term.con 5)) p []) ⟶
  (State.halt (Value.vCon 5)) := by
    repeat (first
      | apply small_step.computeApp
      | apply small_step.computeLambda
      | apply small_step.retLeftAppTerm
      | apply small_step.computeConstant
      | apply small_step.retRightApp
      | apply small_step.computeLookup
      | simp [lookup_var]
        rfl
      | apply small_step.ret
      | apply small_step.seq)


theorem builtin_apply_add_integer
  {p}:
  (State.compute (Term.app (Term.app (Term.builtin (Builtin.mk .addInteger) ) (Term.con 2)) (Term.con 3)) p []) ⟶
  (State.halt (Value.vCon 5)) := by
    apply small_step.seq
    apply small_step.computeApp
    apply small_step.seq
    apply small_step.computeApp
    apply small_step.seq
    apply small_step.computeBuiltin
    apply small_step.seq
    apply small_step.retLeftAppTerm
    apply small_step.seq
    apply small_step.computeConstant
    apply small_step.seq
    apply small_step.retRightAppBuiltin
    case h =>
      simp [not_all_args_applied]

    case h' =>
      apply small_step.seq
      apply small_step.retLeftAppTerm
      apply small_step.seq
      apply small_step.computeConstant
      apply small_step.seq
      apply small_step.retRightAppBuiltin
      case h =>
        simp [not_all_args_applied, builtin_arity, builtin_size, builtin_args, builtin_name]
      case h' =>
        apply small_step.seq
        case h =>
          apply small_step.builtinEval
          case h =>
            simp [builtin_arity, builtin_size, builtin_args, builtin_name, force_size]
          case h' =>
            simp [eval_builtin, builtin_arity, builtin_size, builtin_args, builtin_name, force_size]
            rfl
        case h' =>
          apply small_step.ret


-- theorem builtin_apply_add_integer2
--   {p}:
--   (State.compute (Term.app (Term.app (Term.builtin (Builtin.mk .addInteger) ) (Term.con 2)) (Term.con 3)) p []) ⟶
--   (State.halt (Value.vCon 5)) := by
--     repeat (first
--       | apply small_step.computeApp
--       | apply small_step.computeBuiltin
--       | apply small_step.retLeftAppTerm
--       | apply small_step.computeConstant
--       | apply small_step.retRightAppBuiltin
--       | simp [not_all_args_applied]
--       | simp [not_all_args_applied, builtin_arity, builtin_size, builtin_args, builtin_name]
--       | apply small_step.builtinEval
--       | simp [builtin_arity, builtin_size, builtin_args, builtin_name, force_size]
--       | simp [eval_builtin, builtin_arity, builtin_size, builtin_args, builtin_name, force_size]
--         rfl
--       | apply small_step.ret
--       | apply small_step.seq)
