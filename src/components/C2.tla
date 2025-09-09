--------------------------------- MODULE C2 ---------------------------------
EXTENDS Integers
VARIABLES x, y
vars == <<x, y>>

TypeOK ==
  /\ x \in Int
  /\ y \in -1..1

Init ==
  /\ x \in Int
  /\ y = 0

Next ==
  /\ \/ /\ x >= 1 /\ y < 1
        /\ y' = y + 1
     \/ /\ x < 1 /\ y > -1
        /\ y' = y - 1
  /\ UNCHANGED x

Spec ==
  /\ Init
  /\ [][Next]_vars
=============================================================================
