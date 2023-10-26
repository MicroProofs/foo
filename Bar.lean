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
  | compute (m : Term) (ρ : List (String × Value)) (s : Stack) : State
  | ret (v : Value) (s : Stack) : State
  | error : State
  | halt (v: Value) : State
deriving Repr


def lookupVar (e: List (String × Value)) (x: String) : Option Value :=
  match e with
  | []  => none
  | (y, v) :: e => if x == y then some v else lookupVar e x

inductive big_step : State -> State -> Prop
  | computeLookup {x p s} :
    big_step (State.compute (Term.var x) p s) (match lookupVar p x with | none => State.error | some v => State.ret v s)
  | computeConstant {c p s} : big_step (State.compute (Term.con c) p s) (State.ret (Value.vCon c) s)
  -- | State.ret (Value.vBuiltin b) (Frame.force :: s) : reduc (State.ret (Value.vBuiltin (BuiltinValue.force b)) s)
  | catchAll {s} : big_step s State.error


partial def reduc (st : State) : State :=
  match st with
  | State.compute (Term.var x) ρ s => match lookupVar ρ x with
    | none => State.error
    | some v => reduc (State.ret v s)
  | State.compute (Term.con c) _ s => reduc (State.ret (Value.vCon c) s)
  | State.compute (Term.lam x m) ρ s => reduc (State.ret (Value.vLam x m ρ) s)
  | State.compute (Term.delay m) ρ s => reduc (State.ret (Value.vDelay m ρ) s)
  | State.compute (Term.force m) ρ s => reduc (State.compute m ρ (Frame.force :: s))
  | State.compute (Term.app m n) p s => reduc (State.compute m p (Frame.leftAppTerm n p :: s))
  | State.compute (Term.builtin b) _ s => reduc (State.ret (Value.vBuiltin (BuiltinValue.builtin b)) s)
  | State.compute Term.error _ _ => State.error
  | State.ret v [] => State.halt v
  | State.ret v (Frame.leftAppTerm m p :: s) => reduc (State.compute m p (Frame.rightApp v :: s))
  | State.ret v (Frame.rightApp (Value.vLam x m p) :: s) => reduc (State.compute m ((x, v) :: p) s)
  | State.ret (Value.vLam x m p) (Frame.leftAppValue v :: s) => reduc (State.compute m ((x, v) :: p) s)
  | State.ret v (Frame.rightApp (Value.vBuiltin b) :: s) => reduc (State.ret (Value.vBuiltin (BuiltinValue.app b v)) s)
  | State.ret (Value.vBuiltin b) (Frame.leftAppValue v :: s) => reduc (State.ret (Value.vBuiltin (BuiltinValue.app b v)) s)
  -- TODO: Eval builtins
  | State.ret (Value.vDelay m p) (Frame.force :: s) => reduc (State.compute m p s)
  | State.ret (Value.vBuiltin b) (Frame.force :: s) => reduc (State.ret (Value.vBuiltin (BuiltinValue.force b)) s)
  | _ => State.error

def run (p: Program) : State :=
  reduc (State.compute p.m [] [])

def test2 : State :=
  let x := run ({v := 0, m := Term.app (Term.lam "so" (Term.var "so")) (Term.con 5)})
  x


#eval test2
