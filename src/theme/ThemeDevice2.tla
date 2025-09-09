---------------------------- MODULE ThemeDevice2 -----------------------------
EXTENDS ThemeCommon2, TLAPS
VARIABLES packs, selectedPack, knownIds, request, reply
vars == <<packs, selectedPack, knownIds, request, reply>>

TypeOK ==
  /\ packs \in (SUBSET Pack) \ {{}}
  /\ selectedPack \in packs
  /\ knownIds \in SUBSET Id
  /\ request \in (Request \union {NoRequest})
  /\ reply \in (Reply \union {NoReply})

Init ==
  /\ packs = {InitialPack}
  /\ selectedPack = InitialPack
  /\ knownIds = {}
  /\ request = NoRequest
  /\ reply = NoReply

DeviceSendsListRequest ==
  /\ request = NoRequest
  /\ reply = NoReply
  /\ packs /= Pack
  /\ request' = [op |-> "list"]
  /\ UNCHANGED <<packs, selectedPack, knownIds, reply>>

DeviceReceivesListReply ==
  /\ reply \in [op : {"list"}, ids : SUBSET Id]
  /\ reply' = NoReply
  /\ knownIds' = knownIds \union reply.ids
  /\ UNCHANGED <<packs, selectedPack, request>>

DeviceSendsGetRequest ==
  /\ request = NoRequest
  /\ reply = NoReply
  /\ \E id \in knownIds :
       /\ PackFromId[id] \notin packs
       /\ request' = [op |-> "get", id |-> id]
       /\ UNCHANGED <<packs, selectedPack, knownIds, reply>>

DeviceReceivesGetReply ==
  /\ reply \in [op : {"get"}, pack : Pack]
  /\ reply' = NoReply
  /\ packs' = packs \union {reply.pack}
  /\ UNCHANGED <<selectedPack, knownIds, request>>

UserSelectsATheme ==
  \E p \in packs :
    /\ PackTheme[p] /= PackTheme[selectedPack]
    /\ IsNewestOfItsTheme(p, packs)
    /\ selectedPack' = p
    /\ UNCHANGED <<packs, knownIds, request, reply>>

UserUpgradesSelectedTheme ==
  \E p \in packs :
    /\ PackTheme[p] = PackTheme[selectedPack]
    /\ PackVersion[p] > PackVersion[selectedPack]
    /\ selectedPack' = p
    /\ UNCHANGED <<packs, knownIds, request, reply>>

Next ==
  \* Internal:
    \/ DeviceSendsListRequest
    \/ DeviceReceivesListReply
    \/ DeviceSendsGetRequest
    \/ DeviceReceivesGetReply
  \* Environment:
    \/ UserSelectsATheme
    \/ UserUpgradesSelectedTheme

Spec ==
  /\ Init
  /\ [][Next]_vars

-----------------------------------------------------------------------------
LEMMA InitTypeOK == Init => TypeOK
BY Assumptions2 DEF Init, TypeOK

LEMMA NextTypeOK == TypeOK /\ [Next]_vars => TypeOK'
BY Assumptions2 DEF TypeOK, Next, vars,
  DeviceSendsListRequest, DeviceReceivesListReply, DeviceSendsGetRequest, DeviceReceivesGetReply,
  UserSelectsATheme, UserUpgradesSelectedTheme

THEOREM InvariantTypeOK == Spec => []TypeOK
BY InitTypeOK, NextTypeOK, PTL DEF Spec
-----------------------------------------------------------------------------
Device1 == INSTANCE ThemeDevice1 WITH
  packs <- packs,
  selectedPack <- selectedPack,
  newPack <- NewPack(reply)

LEMMA InitRefinesDevice1Init == Init => Device1!Init
BY Assumptions2 DEF Init, Device1!Init

LEMMA NextRefinesDevice1Next == ASSUME TypeOK /\ [Next]_vars
                               PROVE [Device1!Next]_Device1!vars
<1> USE DEF Device1!vars
<1>1. DeviceSendsListRequest => UNCHANGED Device1!vars
  BY DEF DeviceSendsListRequest
<1>2. DeviceReceivesListReply => UNCHANGED Device1!vars
  BY NoSetContainsEverything, Assumptions2, Zenon
    DEF DeviceReceivesListReply
<1>3. DeviceSendsGetRequest => UNCHANGED Device1!vars
  BY DEF DeviceSendsGetRequest
<1>4. DeviceReceivesGetReply => Device1!ReceivesNewPack
  <2> SUFFICES ASSUME DeviceReceivesGetReply PROVE Device1!ReceivesNewPack
    OBVIOUS
  <2> USE Assumptions2
  <2>1. NewPack(reply) /= NoPack
    BY DEF DeviceReceivesGetReply, TypeOK
  <2>2. packs' = packs \union {NewPack(reply)}
    <3> SUFFICES reply.pack = NewPack(reply)
      BY DEF DeviceReceivesGetReply, Device1!ReceivesNewPack
    <3> QED
      BY DEF DeviceReceivesGetReply, TypeOK
  <2>3. NewPack(reply') = NoPack
    BY DEF DeviceReceivesGetReply
  <2>4. UNCHANGED selectedPack
    BY DEF DeviceReceivesGetReply
  <2>5. QED
    BY <2>1, <2>2, <2>3, <2>4 DEF Next, DeviceReceivesGetReply, Device1!ReceivesNewPack
<1>5. UserSelectsATheme => Device1!UserSelectsATheme
  BY Assumptions DEF UserSelectsATheme, Device1!UserSelectsATheme
<1>6. UserUpgradesSelectedTheme => Device1!UserUpgradesSelectedTheme
  BY Assumptions DEF UserUpgradesSelectedTheme, Device1!UserUpgradesSelectedTheme
<1>7. UNCHANGED vars => UNCHANGED Device1!vars
  BY DEF vars, Device1!vars
<1>8. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 DEF Next, Device1!Next

THEOREM RefinesDevice1 == Spec => Device1!Spec
BY InitRefinesDevice1Init, NextRefinesDevice1Next, InvariantTypeOK, PTL DEF Spec, Device1!Spec
=============================================================================
