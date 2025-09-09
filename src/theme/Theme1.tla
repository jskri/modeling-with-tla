------------------------------- MODULE Theme1 --------------------------------
EXTENDS ThemeCommon1
VARIABLES devicePacks, selectedPack
vars == <<devicePacks, selectedPack>>

TypeOK ==
  /\ devicePacks \in (SUBSET Pack) \ {{}}
  /\ selectedPack \in devicePacks

MinPack(packs, theme) ==
  CHOOSE p1 \in packs:
    \A p2 \in packs:
      (PackTheme[p1] = PackTheme[p2]) => (PackVersion[p1] <= PackVersion[p2])

MinVersion(packs, theme) ==
  IF \E p \in packs: PackTheme[p] = theme
  THEN PackVersion[MinPack(packs, theme)]
  ELSE 0

PackVersionsAreIncreasing ==
  \A t \in Theme:
    MinVersion(devicePacks', t) >= MinVersion(devicePacks, t)

Init ==
  /\ devicePacks = {InitialPack}
  /\ selectedPack = InitialPack

UserSelectsATheme ==
  \E p \in devicePacks:
    /\ PackTheme[p] /= PackTheme[selectedPack]
    /\ IsNewestOfItsTheme(p, devicePacks)
    /\ selectedPack' = p
    /\ UNCHANGED devicePacks

UserUpgradesSelectedTheme ==
  \E p \in devicePacks:
    /\ PackTheme[p] = PackTheme[selectedPack]
    /\ PackVersion[p] > PackVersion[selectedPack]
    /\ selectedPack' = p
    /\ UNCHANGED devicePacks

CompanyAddsAPack ==
  \E p \in Pack:
    /\ p \notin devicePacks
    /\ devicePacks' = devicePacks \union {p}
    /\ UNCHANGED selectedPack

Next ==
  \/ UserSelectsATheme
  \/ UserUpgradesSelectedTheme
  \/ CompanyAddsAPack

Spec ==
  /\ Init
  /\ [][Next]_vars
-----------------------------------------------------------------------------
LEMMA NextTypeOK == TypeOK /\ [Next]_vars => TypeOK'
BY Assumptions DEF TypeOK, Next, vars,
   UserSelectsATheme, UserUpgradesSelectedTheme, CompanyAddsAPack

THEOREM InvariantTypeOK == Spec => []TypeOK
<1>1. Init => TypeOK
  BY Assumptions DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  BY NextTypeOK
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec
=============================================================================