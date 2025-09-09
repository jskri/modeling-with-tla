--------------------------- MODULE WallClockAlarm ----------------------------
\* Module imports
EXTENDS Naturals, TLAPS

\* State
VARIABLES now, alarmDate, ringing
vars == <<now, alarmDate, ringing>>

\* Types
Date == [hour: 1..12, minute: 0..59]

\* Constants
Unset == CHOOSE x : x \notin Date \* Unset is not in Date.

\* Invariants
TypeOK ==
  /\ now \in Date
  /\ alarmDate \in (Date \union {Unset})
  /\ ringing \in BOOLEAN

RingingImpliesAlarmIsSet ==
  ringing => (alarmDate /= Unset)

Init ==
  /\ now \in Date
  /\ alarmDate = Unset
  /\ ringing = FALSE

\* Actions
OneMinuteHasElapsed ==
  LET newHour == IF now.minute = 59 THEN (now.hour % 12) + 1 ELSE now.hour
      newMinute == (now.minute + 1) % 60 IN
    /\ now' = [hour |-> newHour, minute |-> newMinute]
    /\ ringing' = (ringing \/ (now' = alarmDate))
    /\ UNCHANGED alarmDate

UserSetsAlarm ==
  /\ ~ ringing
  /\ \E date \in Date :
       /\ alarmDate' = date
       /\ ringing' = (now = date)
       /\ UNCHANGED now

UserUnsetsAlarm ==
  /\ ~ ringing
  /\ alarmDate /= Unset
  /\ alarmDate' = Unset
  /\ UNCHANGED <<now, ringing>>

UserStopsAlarm ==
  /\ ringing
  /\ ringing' = FALSE
  /\ UNCHANGED <<now, alarmDate>>

\* Specification
Next ==
  \/ OneMinuteHasElapsed
  \/ UserSetsAlarm
  \/ UserUnsetsAlarm
  \/ UserStopsAlarm

Spec ==
  /\ Init
  /\ [][Next]_vars

-----------------------------------------------------------------------------
THEOREM InvariantTypeOK == Spec => []TypeOK
<1>1. Init => TypeOK
  BY Zenon DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2> SUFFICES ASSUME TypeOK /\ [Next]_vars PROVE TypeOK'
    OBVIOUS
  <2> USE DEF TypeOK
  <2>1. CASE OneMinuteHasElapsed
    BY <2>1 DEF OneMinuteHasElapsed, Date
  <2>2. CASE UserSetsAlarm
    BY <2>2 DEF UserSetsAlarm
  <2>3. CASE UserUnsetsAlarm
    BY <2>3 DEF UserUnsetsAlarm
  <2>4. CASE UserStopsAlarm
    BY <2>4, Zenon DEF UserStopsAlarm
  <2>5. CASE UNCHANGED vars
    BY <2>5 DEF vars
  <2>6. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM InvariantRingingImpliesAlarmIsSet == Spec => []RingingImpliesAlarmIsSet
<1>1. Init => RingingImpliesAlarmIsSet
  BY Zenon DEF Init, RingingImpliesAlarmIsSet
<1>2. TypeOK /\ RingingImpliesAlarmIsSet /\ [Next]_vars => RingingImpliesAlarmIsSet'
  <2> SUFFICES ASSUME TypeOK /\ RingingImpliesAlarmIsSet /\ [Next]_vars PROVE RingingImpliesAlarmIsSet'
    OBVIOUS
  <2>1. Unset \notin Date
    BY NoSetContainsEverything DEF Unset
  <2> USE DEF RingingImpliesAlarmIsSet
  <2>2. CASE OneMinuteHasElapsed
    BY <2>1, <2>2 DEF OneMinuteHasElapsed, TypeOK, Date, Unset
  <2>3. CASE UserSetsAlarm
    <3> SUFFICES alarmDate' /= Unset
      OBVIOUS
    <3>1. alarmDate' \in Date
      BY <2>3 DEF UserSetsAlarm
    <3> QED
      BY <2>1, <3>1
  <2>4. CASE UserUnsetsAlarm
    BY <2>4 DEF UserUnsetsAlarm
  <2>5. CASE UserStopsAlarm
    BY <2>5, Zenon DEF UserStopsAlarm
  <2>6. CASE UNCHANGED vars
    BY <2>6 DEF vars
  <2>7. QED
    BY <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next
<1>3. QED
  BY <1>1, <1>2, InvariantTypeOK, PTL DEF Spec

Abstract == INSTANCE WallClock WITH hour <- now.hour, minute <- now.minute

THEOREM RefineAbstract == Spec => Abstract!Spec
<1>1. Init => Abstract!Init
  BY DEF Init, Abstract!Init, Date
<1>2. [Next]_vars => [Abstract!Next]_Abstract!vars
  <2>1. OneMinuteHasElapsed => Abstract!Next
    BY DEF OneMinuteHasElapsed, Abstract!Next
  <2> USE DEF Abstract!vars
  <2>2. UserSetsAlarm => UNCHANGED Abstract!vars
    BY DEF UserSetsAlarm
  <2>3. UserUnsetsAlarm => UNCHANGED Abstract!vars
    BY DEF UserUnsetsAlarm
  <2>4. UserStopsAlarm => UNCHANGED Abstract!vars
    BY DEF UserStopsAlarm
  <2>5. UNCHANGED vars => UNCHANGED Abstract!vars
    BY DEF vars
  <2>6. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec, Abstract!Spec
=============================================================================
