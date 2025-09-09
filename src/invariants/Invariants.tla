----------------------------- MODULE Invariants -----------------------------
EXTENDS Integers, TLAPS
VARIABLES i
vars == i
TypeOK == i \in Nat
Init == i = 0
Next == i' = i + 1
Spec == Init /\ [][Next]_vars

NonNegativeOrMinus5 == (i >= 0) \/ (i = -5)

(* TypeOK is an inductive invariant. *)
THEOREM InvariantTypeOK == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  BY DEF TypeOK, Next, vars
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

(* TypeOK allows one to prove that NonNegativeOrMinus5 is an invariant. *)
THEOREM Spec => []NonNegativeOrMinus5
<1>1. TypeOK => NonNegativeOrMinus5
  BY DEF TypeOK, NonNegativeOrMinus5
<1>2. QED
  BY <1>1, InvariantTypeOK, PTL

(* However, NonNegativeOrMinus5 is not an inductive invariant. *)
THEOREM InvariantNonNegativeOrMinus5 == Spec => []NonNegativeOrMinus5
<1>1. Init => NonNegativeOrMinus5
  BY DEF Init, NonNegativeOrMinus5
<1>2. NonNegativeOrMinus5 /\ [Next]_vars => NonNegativeOrMinus5'
  BY DEF NonNegativeOrMinus5, Next, vars
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec
=============================================================================
