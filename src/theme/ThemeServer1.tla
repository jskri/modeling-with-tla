------------------------------ MODULE ThemeServer1 ------------------------------
EXTENDS ThemeCommon1
VARIABLES packs, unsentPacks, newPack
vars == <<packs, unsentPacks, newPack>>

TypeOK ==
  /\ packs \in (SUBSET Pack) \ {{}}
  /\ unsentPacks \in (SUBSET Pack)
  /\ newPack \in (packs \union {NoPack})

Init ==
  /\ packs = {InitialPack}
  /\ unsentPacks = {}
  /\ newPack = NoPack

ServerSendsAPack ==
  /\ newPack = NoPack
  /\ \E p \in unsentPacks :
       /\ packs' = packs \union {p}
       /\ unsentPacks' = unsentPacks \ {p}
       /\ newPack' = p

CompanyAddsAPack ==
  \E p \in Pack :
    /\ p \notin (packs \union unsentPacks)
    /\ unsentPacks' = unsentPacks \union {p}
    /\ UNCHANGED <<packs, newPack>>

Next ==
  \* Environment:
    \/ CompanyAddsAPack
  \* Internal:
    \/ ServerSendsAPack

Spec ==
  /\ Init
  /\ [][Next]_vars
-----------------------------------------------------------------------------
LEMMA InitTypeOK == Init => TypeOK
BY Assumptions DEF Init, TypeOK

LEMMA NextTypeOK == TypeOK /\ [Next]_vars => TypeOK'
BY Assumptions DEF TypeOK, Next, vars, CompanyAddsAPack, ServerSendsAPack

THEOREM InvariantTypeOK == Spec => []TypeOK
BY InitTypeOK, NextTypeOK, PTL DEF Spec
=============================================================================