---------------------------- MODULE WallClock ----------------------------
(***************************************************************************)
(* This is a model for a basic wall clock with one needle for hours and    *)
(* one for minutes.  The only event is when one minute has elapsed.        *)
(***************************************************************************)

\* Module imports
EXTENDS Naturals

\* State
VARIABLES hour, minute
vars == <<hour, minute>>

\* Invariants
TypeOK ==
  /\ hour \in 1..12
  /\ minute \in 0..59

\* Specification (init & next)

\* The clock can start at any time.
Init ==
  /\ hour \in 1..12
  /\ minute \in 0..59

\* One minute has elapsed: advance the minute needle and maybe the hour one.
Next ==
  /\ hour' = IF minute = 59 THEN (hour % 12) + 1 ELSE hour
  /\ minute' = (minute + 1) % 60

\* The model's formula: initial states must respect `Init` and all steps must
\* respect `Next`.
Spec ==
  /\ Init
  /\ [][Next]_vars
=============================================================================
