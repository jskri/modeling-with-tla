------------------------------- MODULE Theme2 -------------------------------
EXTENDS ThemeCommon1
VARIABLES devicePacks, selectedPack,       \* device vars
          serverPacks, serverUnsentPacks, \* server vars
          newPack                         \* communication vars
vars == <<devicePacks, selectedPack, serverPacks, serverUnsentPacks, newPack>>

Device1 == INSTANCE ThemeDevice1 WITH packs <- devicePacks,
                                    selectedPack <- selectedPack,
                                    newPack <- newPack

Server1 == INSTANCE ThemeServer1 WITH packs <- serverPacks,
                                      unsentPacks <- serverUnsentPacks,
                                      newPack <- newPack

TypeOK ==
  /\ Device1!TypeOK
  /\ Server1!TypeOK

Init ==
  /\ Device1!Init
  /\ Server1!Init

DeviceNext ==
  /\ Device1!Next
  /\ UNCHANGED <<serverPacks, serverUnsentPacks>> \* server vars

ServerNext ==
  /\ Server1!Next
  /\ UNCHANGED <<devicePacks, selectedPack>> \* device vars

Next ==
  \/ DeviceNext
  \/ ServerNext

Spec ==
  /\ Init
  /\ [][Next]_vars
-----------------------------------------------------------------------------
LEMMA InitTypeOK == Init => TypeOK
BY Device1!InitTypeOK, Server1!InitTypeOK, Assumptions DEF Init, TypeOK

LEMMA NextTypeOK == TypeOK /\ [Next]_vars => TypeOK'
<1> SUFFICES ASSUME TypeOK, [Next]_vars PROVE TypeOK'
  OBVIOUS
<1> USE Assumptions DEF TypeOK
<1>1. CASE DeviceNext
  <2>1. Device1!TypeOK'
    BY <1>1, Device1!NextTypeOK DEF DeviceNext
  <2>2. Server1!TypeOK'
    <3> USE <1>1 DEF DeviceNext, Server1!TypeOK
    <3>1. serverPacks' \in (SUBSET Pack) \ {{}}
      OBVIOUS
    <3>2. serverUnsentPacks' \in (SUBSET Pack)
      OBVIOUS
    <3>3. newPack' \in (serverPacks' \union {NoPack})
      BY DEF Device1!UserSelectsATheme, Device1!UserUpgradesSelectedTheme,
             Device1!ReceivesNewPack, Device1!Next
    <3>4. QED
      BY <3>1, <3>2, <3>3 DEF Server1!TypeOK
  <2>3. QED
    BY <2>1, <2>2 DEF TypeOK
<1>2. CASE ServerNext
  <2>1. Server1!TypeOK'
    BY <1>2, Server1!NextTypeOK DEF ServerNext
  <2>2. Device1!TypeOK'
    BY <1>2, <2>1 DEF ServerNext, Device1!TypeOK, Server1!TypeOK
  <2>3. QED
    BY <2>1, <2>2
<1>3. CASE UNCHANGED vars
  BY <1>3, Device1!NextTypeOK, Server1!NextTypeOK
    DEF vars, Device1!vars, Server1!vars
<1>4. QED
  BY <1>1, <1>2, <1>3 DEF Next

THEOREM InvariantTypeOK == Spec => []TypeOK
BY InitTypeOK, NextTypeOK, PTL DEF Spec
-----------------------------------------------------------------------------
DevicePacksInServerPacks ==
  devicePacks \subseteq serverPacks

DevicePacksOlderThanServerPacks ==
  \A p1 \in devicePacks, p2 \in serverPacks :
    PackTheme[p1] = PackTheme[p2] => PackVersion[p1] <= PackVersion[p2]

ServerUnsentPacksNotInDevicePacks ==
  \A p \in serverUnsentPacks : p \notin devicePacks

NewPackProperty ==
  (newPack /= NoPack) => (newPack \in serverPacks /\ newPack \notin devicePacks)

NewPackNotInUnsentPacks ==
  newPack /= NoPack => newPack \notin serverUnsentPacks

Correct ==
  /\ DevicePacksInServerPacks
  /\ ServerUnsentPacksNotInDevicePacks
  /\ NewPackProperty
  /\ NewPackNotInUnsentPacks

LEMMA InvariantCorrect == Spec => []Correct
<1> USE DEF Correct
<1>1. Init => Correct
  BY Assumptions DEF Init, Device1!Init, Server1!Init,
    DevicePacksInServerPacks, ServerUnsentPacksNotInDevicePacks,
    NewPackProperty, NewPackNotInUnsentPacks
<1>2. TypeOK /\ Correct /\ [Next]_vars => Correct'
  <2> SUFFICES ASSUME TypeOK, Correct, [Next]_vars PROVE Correct'
    OBVIOUS
  <2>1. CASE DeviceNext
    <3> USE <2>1 DEF DeviceNext
    <3>1. CASE Device1!UserSelectsATheme /\ UNCHANGED <<serverPacks, serverUnsentPacks>>
      <4> USE <3>1 DEF Device1!UserSelectsATheme
      <4>1. DevicePacksInServerPacks'
        BY DEF DevicePacksInServerPacks
      <4>2. ServerUnsentPacksNotInDevicePacks'
        BY DEF ServerUnsentPacksNotInDevicePacks
      <4>3. NewPackProperty'
        BY DEF NewPackProperty
      <4>4. NewPackNotInUnsentPacks'
        BY DEF NewPackNotInUnsentPacks
      <4>5. QED
        BY <4>1, <4>2, <4>3, <4>4
    <3>2. CASE Device1!UserUpgradesSelectedTheme /\ UNCHANGED <<serverPacks, serverUnsentPacks>>
      <4> USE <3>2 DEF Device1!UserUpgradesSelectedTheme
      <4>1. DevicePacksInServerPacks'
        BY DEF DevicePacksInServerPacks
      <4>2. ServerUnsentPacksNotInDevicePacks'
        BY DEF ServerUnsentPacksNotInDevicePacks
      <4>3. NewPackProperty'
        BY DEF Device1!UserUpgradesSelectedTheme, NewPackProperty
      <4>4. NewPackNotInUnsentPacks'
        BY DEF NewPackNotInUnsentPacks
      <4>5. QED
        BY <3>2, <4>1, <4>2, <4>3, <4>4
    <3>3. CASE Device1!ReceivesNewPack /\ UNCHANGED <<serverPacks, serverUnsentPacks>>
      <4> USE <3>3 DEF Device1!ReceivesNewPack
      <4>1. DevicePacksInServerPacks'
        BY DEF DevicePacksInServerPacks, NewPackProperty
      <4>2. ServerUnsentPacksNotInDevicePacks'
        BY DEF ServerUnsentPacksNotInDevicePacks, NewPackNotInUnsentPacks
      <4>3. NewPackProperty'
        BY DEF NewPackProperty
      <4>4. NewPackNotInUnsentPacks'
        BY DEF NewPackNotInUnsentPacks
      <4>5. QED
        BY <3>3, <4>1, <4>2, <4>3, <4>4
    <3>4. QED
      BY <3>1, <3>2, <3>3 DEF DeviceNext, Device1!Next
  <2>2. CASE ServerNext
    <3> USE <2>2 DEF ServerNext
    <3>1. CASE Server1!ServerSendsAPack /\ UNCHANGED <<devicePacks, selectedPack>>
      <4> USE <3>1 DEF Server1!ServerSendsAPack
      <4>1. DevicePacksInServerPacks'
        BY <3>1 DEF Server1!ServerSendsAPack, DevicePacksInServerPacks
      <4>2. ServerUnsentPacksNotInDevicePacks'
        BY DEF ServerUnsentPacksNotInDevicePacks
      <4>3. NewPackProperty'
        <5> SUFFICES ASSUME newPack = NoPack
                     PROVE newPack' \in serverPacks' /\ newPack' \notin devicePacks'
          BY DEF NewPackProperty
        <5>1. newPack' \in serverPacks'
          BY DEF TypeOK
        <5>2. newPack' \notin devicePacks'
          BY DEF DevicePacksInServerPacks, ServerUnsentPacksNotInDevicePacks
        <5> QED
          BY <5>1, <5>2
      <4>4. NewPackNotInUnsentPacks'
        BY DEF NewPackNotInUnsentPacks
      <4>5. QED
        BY <4>1, <4>2, <4>3, <4>4
    <3>2. CASE Server1!CompanyAddsAPack /\ UNCHANGED <<devicePacks, selectedPack>>
      <4> USE <3>2 DEF Server1!CompanyAddsAPack
      <4>1. DevicePacksInServerPacks'
        BY DEF DevicePacksInServerPacks
      <4>2. ServerUnsentPacksNotInDevicePacks'
        BY <4>1 DEF ServerUnsentPacksNotInDevicePacks, DevicePacksInServerPacks
      <4>3. NewPackProperty'
        BY DEF NewPackProperty
      <4>4. NewPackNotInUnsentPacks'
        BY DEF NewPackNotInUnsentPacks, NewPackProperty
      <4>5. QED
        BY <3>2, <4>1, <4>2, <4>3, <4>4
    <3> QED
      BY <3>1, <3>2 DEF ServerNext, Server1!Next
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF vars, DevicePacksInServerPacks, ServerUnsentPacksNotInDevicePacks,
      NewPackProperty, NewPackNotInUnsentPacks
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next
<1>3. QED
  BY <1>1, <1>2, PTL, InvariantTypeOK DEF Spec
-----------------------------------------------------------------------------
T1 == INSTANCE Theme1

THEOREM RefineTheme1 == Spec => T1!Spec
<1> USE Assumptions
<1>1. Init => T1!Init
  BY DEF Init, Device1!Init, Server1!Init, T1!Init
<1>2. TypeOK /\ Correct /\ [Next]_vars => [T1!Next]_T1!vars
  <2> SUFFICES ASSUME TypeOK, Correct, [Next]_vars PROVE [T1!Next]_T1!vars
    OBVIOUS
  <2>1. ( /\ Device1!UserSelectsATheme
          /\ UNCHANGED <<serverPacks, serverUnsentPacks>> ) => T1!UserSelectsATheme
    BY DEF Device1!UserSelectsATheme, T1!UserSelectsATheme
  <2>2. ( /\ Device1!UserUpgradesSelectedTheme
          /\ UNCHANGED <<serverPacks, serverUnsentPacks>> ) => T1!UserUpgradesSelectedTheme
    BY DEF Device1!UserUpgradesSelectedTheme, T1!UserUpgradesSelectedTheme
  <2>3. ( /\ Device1!ReceivesNewPack
          /\ UNCHANGED <<serverPacks, serverUnsentPacks>> ) => T1!CompanyAddsAPack
    <3> SUFFICES ASSUME newPack /= NoPack
                 PROVE newPack \in Pack /\ newPack \notin devicePacks
      BY DEF Device1!ReceivesNewPack, T1!CompanyAddsAPack
    <3> QED
      BY DEF Correct, NewPackProperty, TypeOK, Server1!TypeOK
  <2>4. ServerNext => UNCHANGED T1!vars
    BY DEF ServerNext, Server1!Next, T1!vars
  <2>5. UNCHANGED vars => UNCHANGED T1!vars
    BY DEF vars, T1!vars
  <2>6. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next, DeviceNext, Device1!Next, T1!Next
<1>3. QED
  BY <1>1, <1>2, InvariantTypeOK, InvariantCorrect, PTL DEF Spec, T1!Spec
=============================================================================