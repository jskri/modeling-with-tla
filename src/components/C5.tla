--------------------------------- MODULE C5 ---------------------------------
(***************************************************************************)
(* Read an integer k and output the number z of distinct integers read so  *)
(* far.                                                                    *)
(***************************************************************************)

EXTENDS Integers, FiniteSets
CONSTANTS Card(_) (* cardinality of a finite set *)
VARIABLES
  k,   (* input integer *)
  _ks, (* private: sets of input integers so far *)
  z    (* number of distinct input integers so far *)
vars == <<k, _ks, z>>

TypeOK ==
  /\ k \in Nat
  /\ _ks = 0..z-1
  /\ z = Card(_ks)

Init ==
  /\ k \in Nat
  /\ _ks = {k}
  /\ z = Card(_ks)

Next ==
  /\ _ks' = _ks \union {k}
  /\ z' = Card(_ks')
  /\ UNCHANGED k

Spec ==
  /\ Init
  /\ [][Next]_vars
=============================================================================
