--------------------------------- MODULE C1 ---------------------------------
CONSTANTS SomeConditionOnC2State(_, _)
VARIABLES x, y, z, k, _ks, c4Turn
c2Vars == <<x, y>>
c3Vars == <<z, k, _ks, c4Turn>>
vars == <<c2Vars, c3Vars>>

C2 == INSTANCE C2 WITH x <- x, y <- y
C3 == INSTANCE C3 WITH z <- z, k <- k, _ks <- _ks, c4Turn <- c4Turn

TypeOK ==
  /\ C2!TypeOK
  /\ C3!TypeOK

Init ==
  /\ C2!Init
  /\ C3!Init
  /\ SomeConditionOnC2State(x, y)

C2Next ==
  /\ SomeConditionOnC2State(x, y)
  /\ C2!Next
  /\ UNCHANGED c3Vars

C3Next ==
  /\ ~ SomeConditionOnC2State(x, y)
  /\ C3!Next
  /\ UNCHANGED c2Vars

Next ==
  \/ C2Next
  \/ C3Next

Spec ==
  /\ Init
  /\ [][Next]_vars
=============================================================================
