--------------------------------- MODULE C3 ---------------------------------
EXTENDS Integers, FiniteSets, TLAPS, FiniteSetTheorems
VARIABLES k, z, _ks, c4Turn
c4Vars == <<k>>
c5Vars == <<z, _ks>>
vars == <<c4Vars, c5Vars, c4Turn>>

C4 == INSTANCE C4 WITH k <- k
C5 == INSTANCE C5 WITH k <- k, _ks <- _ks, z <- z, Card <- Cardinality

TypeOK ==
  /\ C4!TypeOK
  /\ C5!TypeOK
  /\ c4Turn \in BOOLEAN

Init ==
  /\ C4!Init
  /\ C5!Init
  /\ c4Turn = TRUE

C4Next ==
  /\ c4Turn
  /\ C4!Next
  /\ c4Turn' = FALSE
  /\ UNCHANGED c5Vars

C5Next ==
  /\ ~ c4Turn
  /\ C5!Next
  /\ c4Turn' = TRUE
  /\ UNCHANGED c4Vars

Next ==
  \/ C4Next
  \/ C5Next

Spec ==
  /\ Init
  /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Proofs *)

(* Inductive invariant needed to prove refinement. *)
Correct ==
  /\ TypeOK
  /\ k = z - (IF c4Turn THEN 1 ELSE 0)
  /\ ~ c4Turn => k \notin _ks
  /\ IsFiniteSet(_ks)

THEOREM InvCorrect == Spec => []Correct
<1>1. Init => Correct
  BY FS_EmptySet, FS_AddElement DEF Init, C4!Init, C5!Init, Correct, TypeOK, C4!TypeOK, C5!TypeOK
<1>2. Correct /\ [Next]_vars => Correct'
  <2> SUFFICES ASSUME Correct, [Next]_vars PROVE Correct'
    OBVIOUS
  <2>1. CASE C4Next
    <3>1. TypeOK'
      <4> SUFFICES ASSUME k \in 0..10, k \in Nat, _ks = 0..z - 1, z = Cardinality(_ks), c4Turn \in BOOLEAN,
                          c4Turn, k < 10, k' = k + 1, c4Turn' = FALSE, UNCHANGED <<z, _ks>>
                   PROVE k' \in 0..10 /\ k' \in Nat /\ _ks' = 0..z' - 1 /\ z' = Cardinality(_ks') /\ c4Turn' \in BOOLEAN
        BY <2>1, Zenon DEF C4Next, C4!Next, Correct, TypeOK, C4!TypeOK, C5!TypeOK, c5Vars
      <4>1. k' \in 0..10 /\ k' \in Nat OBVIOUS
      <4>2. _ks' = 0..z' - 1 BY Zenon
      <4>3. z' = Cardinality(_ks') OBVIOUS
      <4>4. c4Turn' \in BOOLEAN BY Zenon
      <4>5. QED
        BY <4>1, <4>2, <4>3, <4>4, Zenon
    <3>2. k' = z' - (IF c4Turn' THEN 1 ELSE 0)
      <4> SUFFICES k + 1 = z
        BY <2>1 DEF C4Next, C4!Next, c5Vars
      <4>1. k = z - 1 /\ k' = k + 1
        BY <2>1 DEF Correct, C4Next, C4!Next, c5Vars
      <4>2. QED
        BY <4>1, FS_CardinalityType DEF Correct, TypeOK, C4!TypeOK, C5!TypeOK
    <3>3. ~ c4Turn' => k' \notin _ks'
      <4> USE <2>1 DEF C4Next, C4!Next
      <4>1. _ks' = 0..z - 1
        BY Zenon DEF Correct, TypeOK, C5!TypeOK, c5Vars
      <4>2. k' = z
        BY DEF Correct, TypeOK, C4!TypeOK
      <4>3. ~ c4Turn'
        OBVIOUS
      <4>4. QED
        BY <4>1, <4>2, <4>3
    <3>4. IsFiniteSet(_ks')
      BY <2>1 DEF C4Next, C4!Next, Correct, c5Vars
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Correct
  <2>2. CASE C5Next
    <3>1. TypeOK'
      <4>1. k' \in 0..10 BY <2>2 DEF C5Next, C5!Next, Correct, TypeOK, C4!TypeOK, C5!TypeOK, c4Vars
      <4>2. k' \in Nat BY <2>2 DEF C5Next, C5!Next, Correct, TypeOK, C4!TypeOK, C5!TypeOK, c4Vars
      <4>3. _ks' = 0..z' - 1
        <5> USE DEF C5Next, C5!Next, Correct, TypeOK, C5!TypeOK
        <5>1. z \in Nat
          BY <2>2, FS_CardinalityType
        <5>2. _ks' = 0..z
          <6>1. _ks = 0..z - 1
            BY <2>2
          <6>2. _ks' = _ks \cup {k}
            BY <2>2, Zenon
          <6>3. k = z
            BY <2>2, FS_CardinalityType
          <6>4. QED
            BY <5>1, <6>1, <6>2, <6>3
        <5>3. z' = z + 1
          <6>1. z = Cardinality(_ks)
            BY <2>2
          <6>2. z' = Cardinality(_ks) + 1
              BY <2>2, FS_CardinalityType, FS_AddElement, Zenon
          <6>3. QED
            BY <6>1, <6>2
        <5>4. QED
          BY <5>1, <5>2, <5>3
      <4>4. z' = Cardinality(_ks') BY <2>2 DEF C5Next, C5!Next, Correct, TypeOK, C4!TypeOK, C5!TypeOK, c4Vars
      <4>5. c4Turn' \in BOOLEAN BY <2>2 DEF C5Next, C5!Next, Correct, TypeOK, C4!TypeOK, C5!TypeOK, c4Vars
      <4>6. QED
        BY <4>1, <4>2, <4>3, <4>4, <4>5 DEF TypeOK, C4!TypeOK, C5!TypeOK
    <3>2. k' = z' - (IF c4Turn' THEN 1 ELSE 0)
      <4> SUFFICES k = Cardinality(_ks \cup {k}) - 1
        BY <2>2 DEF C5Next, C5!Next, c4Vars
      <4>1. Cardinality(_ks \cup {k}) = Cardinality(_ks) + 1
        BY <2>2, FS_AddElement, Zenon DEF C5Next, C5!Next, c4Vars, Correct, TypeOK, C4!TypeOK, C5!TypeOK
      <4>2. Cardinality(_ks) = k
        BY <2>2, FS_AddElement DEF C5Next, C5!Next, c4Vars, Correct, TypeOK, C4!TypeOK, C5!TypeOK
      <4>3. Cardinality(_ks \cup {k}) = k + 1
        BY <4>1, <4>2
      <4>4. QED
        BY <4>3 DEF Correct, TypeOK, C4!TypeOK
    <3>3. ~ c4Turn' => k' \notin _ks'
      BY <2>2 DEF C5Next, C5!Next, Correct
    <3>4. IsFiniteSet(_ks')
      BY <2>2, FS_AddElement DEF C5Next, C5!Next, Correct
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Correct
  <2>3. CASE UNCHANGED vars
    BY <2>3, Zenon DEF vars, c4Vars, c5Vars, Correct, TypeOK, C4!TypeOK, C5!TypeOK
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

C3A == INSTANCE C3Abstract WITH
  k <- IF c4Turn THEN k ELSE k - 1,
  z <- z

THEOREM Refinement == Spec => C3A!Spec
<1>1. Init => C3A!Init
  BY FS_EmptySet, FS_AddElement DEF Init, C4!Init, C5!Init, C3A!Init
<1>2. Correct /\ [Next]_vars => [C3A!Next]_C3A!vars
  <2> SUFFICES ASSUME Correct, [Next]_vars PROVE [C3A!Next]_C3A!vars
    OBVIOUS
  <2>1. ASSUME C4Next PROVE UNCHANGED C3A!vars
    BY <2>1 DEF C4Next, C4!Next, c5Vars, C3A!vars, Correct, TypeOK, C4!TypeOK
  <2>2. ASSUME C5Next PROVE C3A!Next
    <3> SUFFICES ASSUME k \in 0..10, _ks = 0..z - 1, z = Cardinality(_ks), ~ c4Turn,
                        UNCHANGED k, _ks' = _ks \cup {k}, z' = Cardinality(_ks'), c4Turn'
                 PROVE /\ k - 1 < 10
                       /\ k' = (k - 1) + 1
                       /\ z' = z + 1
      BY <2>2, Zenon DEF C5Next, C5!Next, c4Vars, c5Vars, C3A!Next, Correct, TypeOK, C4!TypeOK, C5!TypeOK
    <3>1. z' = z + 1
      <4>1. z' = Cardinality(_ks) + 1
        BY z' = Cardinality(_ks \union {k}), k \notin _ks, FS_AddElement, Zenon DEF Correct
      <4>2. QED
        BY <4>1, Cardinality(_ks) = z DEF Correct
    <3>2. QED
      BY <3>1
  <2>3. ASSUME UNCHANGED vars PROVE UNCHANGED C3A!vars
    BY <2>3 DEF vars, c4Vars, c5Vars, C3A!vars
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next
<1>3. QED
  BY <1>1, <1>2, InvCorrect, PTL DEF Spec, C3A!Spec
=============================================================================
