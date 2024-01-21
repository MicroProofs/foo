


-- Term and Program Structures
def Name := String
deriving Repr

inductive Function where
  | addInteger : Function
  | subtractInteger : Function
  | multiplyInteger: Function
  | lessThanInteger : Function
  | lessThanEqualsInteger : Function
  | equalsInteger: Function
deriving Repr

def builtin_arity (function: Function): Nat × Nat :=
  match function with
  | .addInteger => (0, 2)
  | .subtractInteger => (0, 2)
  | .multiplyInteger => (0, 2)
  | .lessThanInteger => (0, 2)
  | .lessThanEqualsInteger => (0, 2)
  | .equalsInteger => (0, 2)


inductive Constant where
  | integer (i: Int) : Constant
  | bool (b: Bool) : Constant
deriving Repr


inductive Term where
  | var (x : String) : Term
  | builtin (b: Function): Term
  | con (c : Constant) : Term
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
  | vCon (c : Constant) : Value
  | vLam (x: String) (m : Term) (p: List (String × Value)) : Value
  | vDelay (m : Term) (p: List (String × Value)) : Value
  | vBuiltin (b: BuiltinValue): Value
deriving Repr

inductive BuiltinValue where
  | builtin (b: Function): BuiltinValue
  | app (b: BuiltinValue) (v: Value): BuiltinValue
  | force (b: BuiltinValue): BuiltinValue
deriving Repr
end

-- Partial Builtin functions
def builtin_name (b: BuiltinValue): Function :=
  match b with
    | .builtin b => b
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

  have j: 0 < List.length args := by
    simp [args_length_is_arity, h, builtin_arity]
    cases builtin_name b with
      | _ => simp

  have jj: 1 < List.length args := by
    simp [args_length_is_arity, h, builtin_arity]
    cases builtin_name b with
      | _ => simp

  match (builtin_name b) with
    | .addInteger => match (args[0], args[1]) with
      | (Value.vCon (Constant.integer l), Value.vCon (Constant.integer r)) =>
        State.ret (Value.vCon (Constant.integer (l + r))) s
      | (_, _) => State.error

    | .subtractInteger => match (args[0], args[1]) with
      | (Value.vCon (Constant.integer l), Value.vCon (Constant.integer r)) =>
        State.ret (Value.vCon (Constant.integer (l - r))) s
      | (_, _) => State.error

    | .lessThanInteger => match (args[0], args[1]) with
      | (Value.vCon (Constant.integer l), Value.vCon (Constant.integer r)) =>
        State.ret (Value.vCon (Constant.bool (l < r))) s
      | (_, _) => State.error

    | .lessThanEqualsInteger => match (args[0], args[1]) with
      | (Value.vCon (Constant.integer l), Value.vCon (Constant.integer r)) =>
        State.ret (Value.vCon (Constant.bool (l <= r))) s
      | (_, _) => State.error

    | .equalsInteger => match (args[0], args[1]) with
      | (Value.vCon (Constant.integer l), Value.vCon (Constant.integer r)) =>
        State.ret (Value.vCon (Constant.bool (l == r))) s
      | (_, _) => State.error

    | .multiplyInteger => match (args[0], args[1]) with
      | (Value.vCon (Constant.integer l), Value.vCon (Constant.integer r)) =>
        State.ret (Value.vCon (Constant.integer (l * r))) s
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

  | builtinEval {b s} (h: builtin_size b = builtin_arity (builtin_name b)) (h': eval_builtin s b h = State.ret v s) : small_step (State.ret (Value.vBuiltin b) s) (State.ret v s)

  | builtinEvalError {b s} (h: builtin_size b = builtin_arity (builtin_name b)) (h': eval_builtin s b h = State.error) : small_step (State.ret (Value.vBuiltin b) s) (State.error)

  | retForceDelay {m p s} : small_step (State.ret (Value.vDelay m p) (Frame.force :: s)) (State.compute m p s)

  | retForceBuiltin {b s} : small_step (State.ret (Value.vBuiltin b) (Frame.force :: s)) (State.ret (Value.vBuiltin (BuiltinValue.force b)) s)

  | catchAll {s} : small_step s State.error


infix: 100 "⟶" => small_step

syntax:max "Term|" term : term

syntax:max "Type|" term : term

syntax:max "Builtin|" term : term

syntax:max "var/" term : term

macro_rules
| `(Term|(lam $x $m)) => `(Term.lam $x (Term|$m))
| `(Term|[var/$x var/$y]) => `(Term.app (Term.var $x) (Term.var $y))
| `(Term|var/$x) => `(Term.var $x)
| `(Term|[$m $n]) => `(Term.app (Term|$m) (Term|$n))
| `(Term|(force $m)) => `(Term.force (Term|$m))
| `(Term|(delay $m)) => `(Term.delay (Term|$m))
| `(Term|(error)) => `(Term.error)
| `(Term|(con $t $c)) => `(Term.con (Type|$t $c))
| `(Term|(builtin $b)) => `(Term.builtin (Builtin| $b))
| `(Term|$t) => `($t)


macro_rules
| `(Type|integer $c) => `(Constant.integer $c)
| `(Type|bool $c) => `(Constant.bool $c)



macro_rules
| `(Builtin|addInteger) => `(Function.addInteger)
| `(Builtin|subtractInteger) => `(Function.subtractInteger)
| `(Builtin|multiplyInteger) => `(Function.multiplyInteger)
| `(Builtin|lessThanInteger) => `(Function.lessThanInteger)
| `(Builtin|lessThanEqualsInteger) => `(Function.lessThanEqualsInteger)
| `(Builtin|equalsInteger) => `(Function.equalsInteger)



-- notation: max "(lam " name:max body:max ")" => Term.lam name body
-- notation: max "(delay " body:max ")" => Term.delay body
-- notation: max "(force " body:max ")" => Term.force body

def x := (Term| (con integer 5))
def y {f x} := (Term| (lam f (lam x [var/f  var/x])))
def z := (Term| (builtin addInteger))


theorem small_step_compute_lambda
{x m p s} : (State.compute (Term|(lam x m)) p s) ⟶ (State.ret (Value.vLam x m p) s) := by
  apply small_step.computeLambda


theorem frame_force_delay_just_term
  {m p s}:
  (State.compute (Term|(delay m)) p (Frame.force :: s)) ⟶
  (State.compute m p s) := by
    have h': (State.compute  (Term|(delay m)) p (Frame.force :: s)) ⟶
      (State.ret (Value.vDelay m p) (Frame.force :: s)) := by
        apply small_step.computeDelay
    have h'': (State.ret (Value.vDelay m p) (Frame.force :: s)) ⟶
      (State.compute m p s) := by
        apply small_step.retForceDelay
    exact small_step.seq h' h''

theorem forcing
  {m p s}:
  (State.compute (Term|(force (force m))) p (s)) ⟶
  (State.compute m p (Frame.force :: Frame.force :: s)) := by
    exact small_step.seq small_step.computeForce small_step.computeForce


theorem force_delay_just_term
  {m p s}:
  (State.compute (Term|(force (delay m))) p s) ⟶
  (State.compute m p s) := by
    have h: (State.compute (Term|(force (delay m))) p s) ⟶
      (State.compute (Term|(delay m)) p (Frame.force :: s)) := by
        apply small_step.computeForce
    have h': (State.compute (Term|(delay m)) p (Frame.force :: s)) ⟶
      (State.ret (Value.vDelay m p) (Frame.force :: s)) := by
        apply small_step.computeDelay
    have h'': (State.ret (Value.vDelay m p) (Frame.force :: s)) ⟶
      (State.compute m p s) := by
        apply small_step.retForceDelay
    exact small_step.seq (small_step.seq h h') h''

theorem double_force_term
  {m p s}:
  (State.compute (Term|(force (force m))) p s) ⟶
  (State.compute m p (Frame.force :: Frame.force :: s)) := by
    have h: (State.compute (Term|(force (force m))) p s) ⟶
      (State.compute (Term|(force m)) p (Frame.force :: s)) := by
        apply small_step.computeForce
    let s' := Frame.force :: s
    have h': (State.compute (Term|(force m)) p s') ⟶
      (State.compute m p (Frame.force :: s')) := by
        apply small_step.computeForce
    exact small_step.seq h h'

theorem force_delay_term
  {m p s}:
  (State.compute (Term|(force (force (delay (delay m))))) p s) ⟶
  (State.compute m p s) := by
    have h: (State.compute (Term|(force (force (delay (delay m))))) p s) ⟶
      (State.compute (Term|(force (delay (delay m)))) p (Frame.force :: s)) := by
        apply small_step.computeForce
    have h': (State.compute (Term|(force (delay (delay m)))) p (Frame.force :: s)) ⟶
      (State.compute (Term|(delay m)) p (Frame.force :: s)) := by
        exact force_delay_just_term
    have h'': (State.compute (Term|(delay m)) p (Frame.force :: s)) ⟶
      (State.compute m p s) := by
        apply frame_force_delay_just_term
    exact small_step.seq (small_step.seq h h') h''

theorem forces
  {m p s}:
  (State.compute (Term|(force (force (force (delay (delay (delay m))))))) p s) ⟶
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
  (State.compute (Term|(force (force (force (delay (delay (delay m))))))) p s) ⟶
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
  (State.compute (Term|(force (force (force (delay (delay (delay m))))))) p s) ⟶
  (State.compute m p s) := by
    repeat (first | apply small_step.computeForce | apply small_step.computeDelay | apply small_step.retForceDelay | apply small_step.seq)



theorem lam_apply_var_is_applied_term
  {x p}:
  (State.compute (Term|[(lam x var/x) (con integer 5)]) p []) ⟶
  (State.halt (Value.vCon (.integer 5))) := by
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
                apply small_step.computeLookup
                case h =>
                  simp [lookup_var]
                  rfl
              case h' => exact small_step.ret






theorem lam_apply_var_is_applied_term2
  {x p}:
  (State.compute (Term|[ (lam x var/x) (con integer 5)]) p []) ⟶
  (State.halt (Value.vCon (.integer 5))) := by
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
  (State.compute (Term| [[(builtin addInteger) (con integer 2)] (con integer 3)]) p []) ⟶
  (State.halt (Value.vCon (.integer 5))) := by
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
      rw [not_all_args_applied]
      simp

    case h' =>
      apply small_step.seq
      apply small_step.retLeftAppTerm
      apply small_step.seq
      apply small_step.computeConstant
      apply small_step.seq
      apply small_step.retRightAppBuiltin
      case h =>
        rw [not_all_args_applied]
        simp [builtin_arity, builtin_size, builtin_args, builtin_name]
      case h' =>
        apply small_step.seq
        case h =>
          apply small_step.builtinEval
          case h =>
            rw [builtin_arity, builtin_size]
            simp [force_size, builtin_name, builtin_args]
          case h' =>
            rw [eval_builtin]
            simp [builtin_args, builtin_name]
            rfl
        case h' =>
          apply small_step.ret


theorem builtin_apply_add_integer2
  {p}:
  (State.compute (Term| [[(builtin addInteger) (con integer 2)] (con integer 3)]) p []) ⟶
  (State.halt (Value.vCon (.integer 5))) := by
    repeat (first
      | apply small_step.computeApp
      | apply small_step.computeBuiltin
      | apply small_step.retLeftAppTerm
      | apply small_step.computeConstant
      | apply small_step.retRightAppBuiltin
      | apply small_step.builtinEval
      | apply small_step.builtinEvalError
      | rw [not_all_args_applied]
        simp [builtin_arity, builtin_size, builtin_args, builtin_name]
      | rw [eval_builtin]
        simp [builtin_args, builtin_name]
        rfl
      | rw [builtin_arity, builtin_size]
        simp [force_size, builtin_name, builtin_args]
      | apply small_step.ret
      | apply small_step.seq)



theorem builtin_apply_sub_integer
  {p}:
  (State.compute (Term| [[(builtin subtractInteger) (con integer 2)] (con integer 3)]) p []) ⟶
  (State.halt (Value.vCon (.integer (-1)))) := by
    repeat (first
      | apply small_step.computeApp
      | apply small_step.computeBuiltin
      | apply small_step.retLeftAppTerm
      | apply small_step.computeConstant
      | apply small_step.retRightAppBuiltin
      | apply small_step.builtinEval
      | apply small_step.builtinEvalError
      | rw [not_all_args_applied]
        simp [builtin_arity, builtin_size, builtin_args, builtin_name]
      | rw [eval_builtin]
        simp [builtin_args, builtin_name]
        rfl
      | rw [builtin_arity, builtin_size]
        simp [force_size, builtin_name, builtin_args]
      | apply small_step.ret
      | apply small_step.seq)


theorem builtin_apply_less_than_integer
  {p} (i: Int) (q: 5 < i):
  (State.compute (Term| [[(builtin lessThanInteger) (con integer 5)] (con integer i)]) p []) ⟶
  (State.halt (Value.vCon (.bool true))) := by
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
      rw [not_all_args_applied]
      simp

    case h' =>
      apply small_step.seq
      apply small_step.retLeftAppTerm
      apply small_step.seq
      apply small_step.computeConstant
      apply small_step.seq
      apply small_step.retRightAppBuiltin
      case h =>
        rw [not_all_args_applied]
        simp [builtin_arity, builtin_size, builtin_args, builtin_name]
      case h' =>
        apply small_step.seq
        case h =>
          apply small_step.builtinEval
          case h =>
            rw [builtin_arity, builtin_size]
            simp [force_size, builtin_name, builtin_args]
          case h' =>
            rw [eval_builtin]
            simp [builtin_args, builtin_name, q]
            rfl
        case h' =>
          exact small_step.ret



theorem builtin_apply_less_than_integer2
  {p} (i: Int) (q: i > 5):
  (State.compute (Term| [[(builtin lessThanInteger) (con integer 5)] (con integer i)]) p []) ⟶
  (State.halt (Value.vCon (.bool (true)))) := by
    repeat (first
      | apply small_step.computeApp
      | apply small_step.computeBuiltin
      | apply small_step.retLeftAppTerm
      | apply small_step.computeConstant
      | apply small_step.retRightAppBuiltin
      | apply small_step.builtinEval
      | apply small_step.builtinEvalError
      | rw [not_all_args_applied]
        simp [builtin_arity, builtin_size, builtin_args, builtin_name]
      | rw [eval_builtin]
        simp [builtin_args, builtin_name, q]
        rfl
      | rw [builtin_arity, builtin_size]
        simp [force_size, builtin_name, builtin_args]
      | apply small_step.ret
      | apply small_step.seq)


-- (program
--   1.0.0
--   [
--     [
--       [
--         (force (force (delay (delay (lam f (lam x [ f x ]))))))
--         (builtin addInteger)
--       ]
--       [
--         (lam
--           x0
--           [
--             [
--               (builtin multiplyInteger)
--               [
--                 [
--                   (builtin subtractInteger)
--                   [
--                     [ (builtin subtractInteger) (con integer 3) ]
--                     (con integer 2)
--                   ]
--                 ]
--                 [ [ (builtin addInteger) (con integer 2) ] (con integer 0) ]
--               ]
--             ]
--             [
--               [
--                 (builtin subtractInteger)
--                 [
--                   [ (builtin multiplyInteger) (con integer 3) ] (con integer 0)
--                 ]
--               ]
--               [ [ (builtin multiplyInteger) (con integer 1) ] (con integer 1) ]
--             ]
--           ]
--         )
--         [
--           [
--             (builtin lessThanEqualsInteger)
--             [
--               [
--                 (builtin subtractInteger)
--                 [
--                   [ (builtin multiplyInteger) (con integer 3) ] (con integer 3)
--                 ]
--               ]
--               [ [ (builtin subtractInteger) (con integer 2) ] (con integer 3) ]
--             ]
--           ]
--           [
--             [
--               (builtin addInteger)
--               [ [ (builtin addInteger) (con integer 2) ] (con integer 3) ]
--             ]
--             [ [ (builtin subtractInteger) (con integer 3) ] (con integer 3) ]
--           ]
--         ]
--       ]
--     ]
--     [
--       (lam
--         x0
--         [
--           (lam
--             x2
--             [
--               [
--                 (builtin addInteger)
--                 [
--                   [ (builtin subtractInteger) (con integer 0) ] (con integer 3)
--                 ]
--               ]
--               [ [ (builtin subtractInteger) (con integer 2) ] (con integer 1) ]
--             ]
--           )
--           [
--             [
--               (builtin subtractInteger)
--               [ [ (builtin addInteger) (con integer 1) ] (con integer 1) ]
--             ]
--             [ [ (builtin subtractInteger) (con integer 2) ] (con integer 0) ]
--           ]
--         ]
--       )
--       [
--         (lam
--           x1
--           [
--             [
--               (builtin lessThanInteger)
--               [ [ (builtin multiplyInteger) (con integer 0) ] (con integer 3) ]
--             ]
--             [ [ (builtin addInteger) (con integer 0) ] (con integer 1) ]
--           ]
--         )
--         [
--           [
--             (builtin equalsInteger)
--             [ [ (builtin multiplyInteger) (con integer 3) ] (con integer 2) ]
--           ]
--           [ [ (builtin subtractInteger) (con integer 2) ] (con integer 0) ]
--         ]
--       ]
--     ]
--   ]
-- )

theorem apply_add_2(f: String) (x: String) :
(State.compute (Term|
  [
    [
      [
        (force (force (delay (delay (lam f (lam x [ var/f var/x ]))))))
        (builtin addInteger)
      ]
      [
        (lam
          x0
          [
            [
              (builtin multiplyInteger)
              [
                [
                  (builtin subtractInteger)
                  [
                    [ (builtin subtractInteger) (con integer 3) ]
                    (con integer 2)
                  ]
                ]
                [ [ (builtin addInteger) (con integer 2) ] (con integer 0) ]
              ]
            ]
            [
              [
                (builtin subtractInteger)
                [
                  [ (builtin multiplyInteger) (con integer 3) ] (con integer 0)
                ]
              ]
              [ [ (builtin multiplyInteger) (con integer 1) ] (con integer 1) ]
            ]
          ]
        )
        [
          [
            (builtin lessThanEqualsInteger)
            [
              [
                (builtin subtractInteger)
                [
                  [ (builtin multiplyInteger) (con integer 3) ] (con integer 3)
                ]
              ]
              [ [ (builtin subtractInteger) (con integer 2) ] (con integer 3) ]
            ]
          ]
          [
            [
              (builtin addInteger)
              [ [ (builtin addInteger) (con integer 2) ] (con integer 3) ]
            ]
            [ [ (builtin subtractInteger) (con integer 3) ] (con integer 3) ]
          ]
        ]
      ]
    ]
    [
      (lam
        x0
        [
          (lam
            x2
            [
              [
                (builtin addInteger)
                [
                  [ (builtin subtractInteger) (con integer 0) ] (con integer 3)
                ]
              ]
              [ [ (builtin subtractInteger) (con integer 2) ] (con integer 1) ]
            ]
          )
          [
            [
              (builtin subtractInteger)
              [ [ (builtin addInteger) (con integer 1) ] (con integer 1) ]
            ]
            [ [ (builtin subtractInteger) (con integer 2) ] (con integer 0) ]
          ]
        ]
      )
      [
        (lam
          x1
          [
            [
              (builtin lessThanInteger)
              [ [ (builtin multiplyInteger) (con integer 0) ] (con integer 3) ]
            ]
            [ [ (builtin addInteger) (con integer 0) ] (con integer 1) ]
          ]
        )
        [
          [
            (builtin equalsInteger)
            [ [ (builtin multiplyInteger) (con integer 3) ] (con integer 2) ]
          ]
          [ [ (builtin subtractInteger) (con integer 2) ] (con integer 0) ]
        ]
      ]
    ]
  ])
   p []) ⟶ (State.halt (Value.vCon (.integer (-1)))) := by sorry
