----------------------------- MODULE C3Abstract -----------------------------
EXTENDS Integers
VARIABLES k, z
vars == <<k, z>>

TypeOK ==
  /\ k \in 0..10
  /\ z \in 1..11

Init ==
  /\ k = 0
  /\ z = 1

Next ==
  /\ k < 10
  /\ k' = k + 1
  /\ z' = z + 1

Spec ==
  /\ Init
  /\ [][Next]_vars
=============================================================================
