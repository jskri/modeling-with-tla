------------------------- MODULE ThemeDevice1 --------------------------
EXTENDS ThemeCommon1
VARIABLES packs, selectedPack, newPack
vars == <<packs, selectedPack, newPack>>

TypeOK ==
  /\ packs \in (SUBSET Pack) \ {{}}
  /\ selectedPack \in packs
  /\ newPack \in (Pack \union {NoPack})

Init ==
  /\ packs = {InitialPack}
  /\ selectedPack = InitialPack
  /\ newPack = NoPack

UserSelectsATheme ==
  \E p \in packs :
    /\ PackTheme[p] /= PackTheme[selectedPack]
    /\ IsNewestOfItsTheme(p, packs)
    /\ selectedPack' = p
    /\ UNCHANGED <<packs, newPack>>

UserUpgradesSelectedTheme ==
  \E p \in packs :
    /\ PackTheme[p] = PackTheme[selectedPack]
    /\ PackVersion[p] > PackVersion[selectedPack]
    /\ selectedPack' = p
    /\ UNCHANGED <<packs, newPack>>

ReceivesNewPack ==
  /\ newPack /= NoPack
  /\ packs' = packs \union {newPack}
  /\ newPack' = NoPack
  /\ UNCHANGED selectedPack

Next ==
  \* Environment:
    \/ UserSelectsATheme
    \/ UserUpgradesSelectedTheme
  \* Internal:
    \/ ReceivesNewPack

Spec ==
  /\ Init
  /\ [][Next]_vars
-----------------------------------------------------------------------------
LEMMA InitTypeOK == Init => TypeOK
BY Assumptions DEF Init, TypeOK

LEMMA NextTypeOK == TypeOK /\ [Next]_vars => TypeOK'
BY Assumptions DEF TypeOK, Next, vars,
   UserSelectsATheme, UserUpgradesSelectedTheme, ReceivesNewPack

THEOREM InvariantTypeOK == Spec => []TypeOK
BY InitTypeOK, NextTypeOK, PTL DEF Spec
=============================================================================
