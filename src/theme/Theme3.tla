------------------------------- MODULE Theme3 -------------------------------
EXTENDS ThemeCommon2
VARIABLES devicePacks, selectedPack, knownIds, \* device vars
          serverPacks, serverUnsentPacks,      \* server vars
          request, reply                       \* communication vars
vars == <<devicePacks, selectedPack, knownIds,
         serverPacks, serverUnsentPacks, request, reply>>

Device2 == INSTANCE ThemeDevice2
  WITH packs <- devicePacks,
       selectedPack <- selectedPack,
       knownIds <- knownIds,
       request <- request,
       reply <- reply

Server2 == INSTANCE ThemeServer2
  WITH packs <- serverPacks,
       unsentPacks <- serverUnsentPacks,
       request <- request,
       reply <- reply

TypeOK ==
  /\ Device2!TypeOK
  /\ Server2!TypeOK

Init ==
  /\ Device2!Init
  /\ Server2!Init

DeviceNext ==
  /\ Device2!Next
  /\ UNCHANGED <<serverPacks, serverUnsentPacks>>

ServerNext ==
  /\ Server2!Next
  /\ UNCHANGED <<devicePacks, selectedPack, knownIds>>

Next ==
  \/ DeviceNext
  \/ ServerNext

Spec ==
  /\ Init
  /\ [][Next]_vars
-----------------------------------------------------------------------------
LEMMA InitTypeOK == Init => TypeOK
BY Device2!InitTypeOK, Server2!InitTypeOK, Assumptions2 DEF Init, TypeOK

LEMMA NextTypeOK == ASSUME TypeOK /\ [Next]_vars PROVE TypeOK'
  <1> USE Assumptions2 DEF TypeOK
  <1>1. CASE DeviceNext
    <2>1. Device2!TypeOK'
      BY <1>1, Device2!NextTypeOK DEF Next, DeviceNext
    <2>2. Server2!TypeOK'
      BY <1>1, <2>1 DEF Server2!TypeOK, Next, DeviceNext, Device2!TypeOK
    <2>3. QED
      BY <2>1, <2>2
  <1>2. CASE ServerNext
    <2>1. Server2!TypeOK'
      BY <1>2, Server2!NextTypeOK DEF Next, ServerNext
    <2>2. Device2!TypeOK'
      BY <1>2, <2>1 DEF Server2!TypeOK, Next, ServerNext, Device2!TypeOK
    <2>3. QED
      BY <2>1, <2>2
  <1>3. CASE UNCHANGED vars
    BY <1>3, Device2!NextTypeOK, Server2!NextTypeOK DEF vars, Device2!vars, Server2!vars
  <1>4. QED
    BY <1>1, <1>2, <1>3 DEF Next

THEOREM InvariantTypeOK == Spec => []TypeOK
BY InitTypeOK, NextTypeOK, PTL DEF Spec
-----------------------------------------------------------------------------
Theme2 == INSTANCE Theme2 WITH newPack <- NewPack(reply)

LEMMA SameInit ==
  /\ Device2!Device1!Init <=> Theme2!Device1!Init
  /\ Server2!Server1!Init <=> Theme2!Server1!Init
BY DEF Device2!Device1!Init, Theme2!Device1!Init,
  Server2!Server1!Init, Theme2!Server1!Init

LEMMA SameDevice1Next == Device2!Device1!Next <=> Theme2!Device1!Next
BY DEF Device2!Device1!Next, Theme2!Device1!Next,
  Device2!Device1!UserSelectsATheme, Theme2!Device1!UserSelectsATheme,
  Device2!Device1!UserUpgradesSelectedTheme, Theme2!Device1!UserUpgradesSelectedTheme,
  Device2!Device1!ReceivesNewPack, Theme2!Device1!ReceivesNewPack

LEMMA SameServer1Next == Server2!Server1!Next <=> Theme2!Server1!Next
BY Assumptions DEF Server2!Server1!Next, Theme2!Server1!Next,
  Server2!Server1!ServerSendsAPack, Theme2!Server1!ServerSendsAPack,
  Server2!Server1!CompanyAddsAPack, Theme2!Server1!CompanyAddsAPack

THEOREM RefinesTheme2 == Spec => Theme2!Spec
<1> USE Assumptions2
<1>1. Init => Theme2!Init
  BY Device2!InitRefinesDevice1Init, Server2!InitRefinesServer1Init, SameInit
    DEF Init, Theme2!Init
<1>2. TypeOK /\ [Next]_vars => [Theme2!Next]_Theme2!vars
  <2> SUFFICES ASSUME TypeOK, [Next]_vars PROVE [Theme2!Next]_Theme2!vars
    OBVIOUS
  <2>1. Device2!TypeOK /\ [Device2!Next]_Device2!vars => [Theme2!Device1!Next]_Theme2!Device1!vars
    <3>1. Device2!TypeOK /\ [Device2!Next]_Device2!vars => [Device2!Device1!Next]_Device2!Device1!vars
      BY Device2!NextRefinesDevice1Next, SameDevice1Next
    <3>2. [Device2!Device1!Next]_Device2!Device1!vars => [Theme2!Device1!Next]_Theme2!Device1!vars
      <4>1. Device2!Device1!Next => Theme2!Device1!Next
        BY SameDevice1Next
      <4>2. UNCHANGED Device2!Device1!vars => UNCHANGED Theme2!Device1!vars
        BY DEF Device2!Device1!vars, Theme2!Device1!vars
      <4>3. QED
        BY <4>1, <4>2
    <3>3. QED
      BY <3>1, <3>2
  <2>2. Server2!TypeOK /\ [Server2!Next]_Server2!vars => [Theme2!Server1!Next]_Theme2!Server1!vars
    <3>1. Server2!TypeOK /\ [Server2!Next]_Server2!vars =>
            [Server2!Server1!Next]_Server2!Server1!vars
      BY Server2!NextRefinesServer1Next
    <3>2. [Server2!Server1!Next]_Server2!Server1!vars =>
            [Theme2!Server1!Next]_Theme2!Server1!vars
      <4>1. Server2!Server1!Next => Theme2!Server1!Next
        BY SameServer1Next
      <4>2. UNCHANGED Server2!Server1!vars => UNCHANGED Theme2!Server1!vars
        BY DEF Server2!Server1!vars, Theme2!Server1!vars
      <4>3. QED
        BY <4>1, <4>2
    <3>3. QED
      BY <3>1, <3>2
  <2>3. UNCHANGED vars => UNCHANGED Theme2!vars
    BY DEF vars, Theme2!vars
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next, Theme2!Next,
      DeviceNext, Theme2!DeviceNext, Theme2!Device1!vars, ServerNext, Theme2!ServerNext,
      Theme2!vars, Theme2!Server1!vars, TypeOK
<1>3. QED
  BY <1>1, <1>2, InvariantTypeOK, PTL DEF Spec, Theme2!Spec
=============================================================================
