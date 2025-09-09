---------------------------- MODULE ThemeServer2 ----------------------------
EXTENDS ThemeCommon2
VARIABLES packs, unsentPacks, request, reply
vars == <<packs, unsentPacks, request, reply>>

TypeOK ==
  /\ packs \in (SUBSET Pack) \ {{}}
  /\ unsentPacks \in (SUBSET Pack)
  /\ request \in (Request \union {NoRequest})
  /\ reply \in (Reply \union {NoReply})

Init ==
  /\ packs = {InitialPack}
  /\ unsentPacks = {}
  /\ request = NoRequest
  /\ reply = NoReply

ServerHandlesListRequest ==
  /\ request \in [op: {"list"}]
  /\ reply = NoReply
  /\ request' = NoRequest
  /\ reply' = [op |-> "list", ids |-> {PackId[p] : p \in unsentPacks}]
  /\ UNCHANGED <<packs, unsentPacks>>

ServerHandlesGetRequest ==
  /\ request \in [op: {"get"}, id: Id]
  /\ \E p \in unsentPacks :
       /\ PackId[p] = request.id
       /\ reply = NoReply
       /\ packs' = packs \union {p}
       /\ unsentPacks' = unsentPacks \ {p}
       /\ request' = NoRequest
       /\ reply' = [op |-> "get", pack |-> p]

CompanyAddsAPack ==
  \E p \in Pack:
    /\ p \notin (packs \union unsentPacks)
    /\ unsentPacks' = unsentPacks \union {p}
    /\ UNCHANGED <<packs, request, reply>>

Next ==
  \* Internal:
    \/ ServerHandlesListRequest
    \/ ServerHandlesGetRequest
  \* Environment:
    \/ CompanyAddsAPack

Spec ==
  /\ Init
  /\ [][Next]_vars
-----------------------------------------------------------------------------
LEMMA InitTypeOK == Init => TypeOK
BY Assumptions2 DEF Init, TypeOK

LEMMA NextTypeOK == TypeOK /\ [Next]_vars => TypeOK'
BY Assumptions2 DEF TypeOK, Next, vars,
  ServerHandlesListRequest, ServerHandlesGetRequest, CompanyAddsAPack

THEOREM InvariantTypeOK == Spec => []TypeOK
BY InitTypeOK, NextTypeOK, PTL DEF Spec
-----------------------------------------------------------------------------
Server1 == INSTANCE ThemeServer1 WITH newPack <- NewPack(reply)

LEMMA InitRefinesServer1Init == ASSUME Init PROVE Server1!Init
BY Assumptions2 DEF Init, Server1!Init

LEMMA NextRefinesServer1Next ==
  ASSUME TypeOK /\ [Next]_vars PROVE [Server1!Next]_Server1!vars
<1> USE Assumptions2
<1>1. ASSUME ServerHandlesListRequest PROVE UNCHANGED Server1!vars
  BY <1>1 DEF ServerHandlesListRequest, Server1!vars, TypeOK
<1>2. ASSUME ServerHandlesGetRequest PROVE Server1!ServerSendsAPack
  <2>1. NewPack(reply) = NoPack
    BY <1>2 DEF ServerHandlesGetRequest
  <2>2. \E p \in unsentPacks:
          /\ packs' = packs \union {p}
          /\ unsentPacks' = unsentPacks \ {p}
          /\ NewPack(reply') = p
    BY <1>2, NextTypeOK DEF ServerHandlesGetRequest, TypeOK
  <2>3. QED
    BY <2>1, <2>2 DEF Server1!ServerSendsAPack
<1>3. ASSUME CompanyAddsAPack PROVE Server1!CompanyAddsAPack
  BY <1>3 DEF CompanyAddsAPack, Server1!CompanyAddsAPack
<1>4. ASSUME UNCHANGED vars PROVE UNCHANGED Server1!vars
  BY <1>4 DEF vars, Server1!vars
<1>5. QED
  BY <1>1, <1>2, <1>3, <1>4 DEF Next, Server1!Next

THEOREM RefinesServer1 == Spec => Server1!Spec
BY InitRefinesServer1Init, NextRefinesServer1Next, PTL, InvariantTypeOK
  DEF Spec, Server1!Spec
=============================================================================