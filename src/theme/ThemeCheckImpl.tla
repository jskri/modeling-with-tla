--------------------------- MODULE ThemeCheckImpl ----------------------------
(***************************************************************************)
(* # Presentation                                                          *)
(*                                                                         *)
(* The goal of this model is to check if an implementation is conform to   *)
(* its specification.                                                      *)
(*                                                                         *)
(* The approach here is not to prove that the implementation is conform    *)
(* (we cannot), only to check that a particular run is conform.  Thus, the *)
(* more runs are checked the better.                                       *)
(*                                                                         *)
(*                                                                         *)
(* # Files                                                                 *)
(*                                                                         *)
(* The specification to check is Theme3.tla.  The implementation is split  *)
(* into a client and a server, respectively src/implementation/client.cpp  *)
(* and src/implementation/server.cpp.                                      *)
(*                                                                         *)
(* The log merger (see below) can be found at                              *)
(* src/implementation/merge_logs.py                                        *)
(*                                                                         *)
(*                                                                         *)
(* # Checking procedure                                                    *)
(*                                                                         *)
(* 1.  Conceptually map the specification to the implementation, i.e.      *)
(* find places in the code that correspond to the specification's actions. *)
(*                                                                         *)
(* 2.  In the found places, add state logs.  Each log must have a          *)
(* timestamp and must describe the current state in terms of the           *)
(* specification's variables.  It should also mention its action to        *)
(* facilitate debugging.                                                   *)
(*                                                                         *)
(* 3.  Set the specification to check as a temporal property of this model *)
(* (see `MSpec` below).                                                    *)
(*                                                                         *)
(* 4.  Run the implementation to produce log file(s).                      *)
(*                                                                         *)
(* 5.  Merge log files if there are several ones.  This can happen when    *)
(* the implementation is split over several components (e.g.  one binary   *)
(* for client and one for server).  The merged log must be ordered by      *)
(* increasing timestamp.                                                   *)
(*                                                                         *)
(* 6.  Complete log entries in order for each entry to describe a complete *)
(* specification's state.  This is typically necessary when there are      *)
(* several implementation components, because each one can only log its    *)
(* local and partial view of the complete (i.e.  global) state.  The       *)
(* result of the completion is a sequence of (global) states.              *)
(*                                                                         *)
(* 7.  Put the sequence of states in this model (see `Trace` below).       *)
(*                                                                         *)
(* 8.  Run the checker.  If the checker finds no error, the run is conform *)
(* to the specification.                                                   *)
(*                                                                         *)
(* 9.  Repeat steps 4 to 8 ad lib.                                         *)
(*                                                                         *)
(*                                                                         *)
(* # Notes                                                                 *)
(*                                                                         *)
(* An interesting feature of this approach is that if the run is not       *)
(* conform, the checker will point the first invalid step.  It is          *)
(* therefore possible to known in a precise way why the implementation is  *)
(* faulty and fix it accordingly.                                          *)
(*                                                                         *)
(*                                                                         *)
(* # Sources                                                               *)
(*                                                                         *)
(* - [Verifying Software Traces Against a Formal Specification with TLA+   *)
(* and TLC](https://pron.github.io/files/Trace.pdf)                        *)
(*                                                                         *)
(* - [eXtreme Modelling in Practice](https://arxiv.org/pdf/2006.00915)     *)
(*                                                                         *)
(***************************************************************************)

EXTENDS ThemeCommon2, Sequences
\* Theme3 variables
VARIABLES devicePacks, selectedPack, knownIds, \* device vars
          serverPacks, serverUnsentPacks,      \* server vars
          request, reply                       \* communication vars
\* Check variables
VARIABLES i
vars == <<devicePacks, selectedPack, knownIds, serverPacks, serverUnsentPacks, request, reply, i>>

Traces == <<
   \* trace 1
  <<
    (* <<devicePacks, selectedPack, knownIds, serverPacks, serverUnsentPacks, request, reply>> *)
    <<{<<1,"t1",1>>}, <<1,"t1",1>>, {}, {<<1,"t1",1>>}, {}, NoRequest, NoReply>>, (* Init (0) *)
    <<{<<1,"t1",1>>}, <<1,"t1",1>>, {}, {<<1,"t1",1>>}, {<<3,"t2",1>>}, NoRequest, NoReply>>, (* CompanyAddsAPack (9443362731087) *)
    <<{<<1,"t1",1>>}, <<1,"t1",1>>, {}, {<<1,"t1",1>>}, {<<3,"t2",1>>}, [op |-> "list"], NoReply>>, (* DeviceSendsListRequest (9444378637548) *)
    <<{<<1,"t1",1>>}, <<1,"t1",1>>, {}, {<<1,"t1",1>>}, {<<3,"t2",1>>}, NoRequest, [op |-> "list", ids |-> {3}]>>, (* ServerHandlesListRequest (9444379447553) *)
    <<{<<1,"t1",1>>}, <<1,"t1",1>>, {3}, {<<1,"t1",1>>}, {<<3,"t2",1>>}, NoRequest, NoReply>>, (* DeviceReceivesListReply (9444379594185) *)
    <<{<<1,"t1",1>>}, <<1,"t1",1>>, {3}, {<<1,"t1",1>>}, {<<3,"t2",1>>}, [op |-> "get", id |-> 3], NoReply>>, (* DeviceSendsGetRequest (9444379623112) *)
    <<{<<1,"t1",1>>}, <<1,"t1",1>>, {3}, {<<1,"t1",1>>}, {<<3,"t2",1>>}, [op |-> "get", id |-> 3], NoReply>>, (* CompanyAddsAPack (9445379823801) *)
    <<{<<1,"t1",1>>}, <<1,"t1",1>>, {3}, {<<1,"t1",1>>,<<3,"t2",1>>}, {}, NoRequest, [op |-> "get", pack |-> <<3,"t2",1>>]>>, (* ServerHandlesGetRequest (9445379882322) *)
    <<{<<1,"t1",1>>,<<3,"t2",0>>}, <<1,"t1",1>>, {3}, {<<1,"t1",1>>,<<3,"t2",1>>}, {}, NoRequest, NoReply>>, (* DeviceReceivesGetReply (9445380281535) *)
    <<{<<1,"t1",1>>,<<3,"t2",0>>}, <<1,"t1",1>>, {3}, {<<1,"t1",1>>,<<3,"t2",1>>}, {<<4,"t2",2>>}, NoRequest, NoReply>>, (* CompanyAddsAPack (9446380112196) *)
    <<{<<1,"t1",1>>,<<3,"t2",0>>}, <<1,"t1",1>>, {3}, {<<1,"t1",1>>,<<3,"t2",1>>}, {<<4,"t2",2>>}, [op |-> "list"], NoReply>>, (* DeviceSendsListRequest (9446380470026) *)
    <<{<<1,"t1",1>>,<<3,"t2",0>>}, <<1,"t1",1>>, {3}, {<<1,"t1",1>>,<<3,"t2",1>>}, {<<4,"t2",2>>}, NoRequest, [op |-> "list", ids |-> {4}]>>, (* ServerHandlesListRequest (9446380863447) *)
    <<{<<1,"t1",1>>,<<3,"t2",0>>}, <<1,"t1",1>>, {3,4}, {<<1,"t1",1>>,<<3,"t2",1>>}, {<<4,"t2",2>>}, NoRequest, NoReply>>, (* DeviceReceivesListReply (9446381194585) *)
    <<{<<1,"t1",1>>,<<3,"t2",0>>}, <<1,"t1",1>>, {3,4}, {<<1,"t1",1>>,<<3,"t2",1>>}, {<<4,"t2",2>>}, [op |-> "get", id |-> 4], NoReply>>, (* DeviceSendsGetRequest (9446381229882) *)
    <<{<<1,"t1",1>>,<<3,"t2",0>>}, <<1,"t1",1>>, {3,4}, {<<1,"t1",1>>,<<3,"t2",1>>}, {<<4,"t2",2>>}, [op |-> "get", id |-> 4], NoReply>>, (* CompanyAddsAPack (9447381231907) *)
    <<{<<1,"t1",1>>,<<3,"t2",0>>}, <<1,"t1",1>>, {3,4}, {<<1,"t1",1>>,<<3,"t2",1>>,<<4,"t2",2>>}, {}, NoRequest, [op |-> "get", pack |-> <<4,"t2",2>>]>>, (* ServerHandlesGetRequest (9447381282823) *)
    <<{<<1,"t1",1>>,<<3,"t2",0>>,<<4,"t2",0>>}, <<1,"t1",1>>, {3,4}, {<<1,"t1",1>>,<<3,"t2",1>>,<<4,"t2",2>>}, {}, NoRequest, NoReply>>, (* DeviceReceivesGetReply (9447381644988) *)
    <<{<<1,"t1",1>>,<<3,"t2",0>>,<<4,"t2",0>>}, <<1,"t1",1>>, {3,4}, {<<1,"t1",1>>,<<3,"t2",1>>,<<4,"t2",2>>}, {}, [op |-> "list"], NoReply>>, (* DeviceSendsListRequest (9448381748485) *)
    <<{<<1,"t1",1>>,<<3,"t2",0>>,<<4,"t2",0>>}, <<1,"t1",1>>, {3,4}, {<<1,"t1",1>>,<<3,"t2",1>>,<<4,"t2",2>>}, {}, NoRequest, [op |-> "list", ids |-> {}]>>, (* ServerHandlesListRequest (9448382150114) *)
    <<{<<1,"t1",1>>,<<3,"t2",0>>,<<4,"t2",0>>}, <<1,"t1",1>>, {3,4}, {<<1,"t1",1>>,<<3,"t2",1>>,<<4,"t2",2>>}, {}, NoRequest, NoReply>>, (* DeviceReceivesListReply (9448382491998) *)
    <<{<<1,"t1",1>>,<<3,"t2",0>>,<<4,"t2",0>>}, <<1,"t1",1>>, {3,4}, {<<1,"t1",1>>,<<3,"t2",1>>,<<4,"t2",2>>}, {}, [op |-> "list"], NoReply>>, (* DeviceSendsListRequest (9449382704371) *)
    <<{<<1,"t1",1>>,<<3,"t2",0>>,<<4,"t2",0>>}, <<1,"t1",1>>, {3,4}, {<<1,"t1",1>>,<<3,"t2",1>>,<<4,"t2",2>>}, {}, NoRequest, [op |-> "list", ids |-> {}]>>, (* ServerHandlesListRequest (9449383029993) *)
    <<{<<1,"t1",1>>,<<3,"t2",0>>,<<4,"t2",0>>}, <<1,"t1",1>>, {3,4}, {<<1,"t1",1>>,<<3,"t2",1>>,<<4,"t2",2>>}, {}, NoRequest, [op |-> "list", ids |-> {}]>> (* ServerHandlesListRequest (9450383787355) *)
  >>,
   \* trace 2
  <<
    (* <<devicePacks, selectedPack, knownIds, serverPacks, serverUnsentPacks, request, reply>> *)
    <<{<<1,"t1",1>>}, <<1,"t1",1>>, {}, {<<1,"t1",1>>}, {}, NoRequest, NoReply>>, (* Init (0) *)
    <<{<<1,"t1",1>>}, <<1,"t1",1>>, {}, {<<1,"t1",1>>}, {}, [op |-> "list"], NoReply>>, (* DeviceSendsListRequest (7772085694465) *)
    <<{<<1,"t1",1>>}, <<1,"t1",1>>, {}, {<<1,"t1",1>>}, {<<3,"t2",1>>}, [op |-> "list"], NoReply>>, (* CompanyAddsAPack (7774157875788) *)
    <<{<<1,"t1",1>>}, <<1,"t1",1>>, {}, {<<1,"t1",1>>}, {<<3,"t2",1>>}, NoRequest, [op |-> "list", ids |-> {3}]>>, (* ServerHandlesListRequest (7774225617855) *)
    <<{<<1,"t1",1>>}, <<1,"t1",1>>, {3}, {<<1,"t1",1>>}, {<<3,"t2",1>>}, NoRequest, NoReply>>, (* DeviceReceivesListReply (7774225991733) *)
    <<{<<1,"t1",1>>}, <<1,"t1",1>>, {3}, {<<1,"t1",1>>}, {<<3,"t2",1>>}, [op |-> "get", id |-> 3], NoReply>>, (* DeviceSendsGetRequest (7774226020613) *)
    <<{<<1,"t1",1>>}, <<1,"t1",1>>, {3}, {<<1,"t1",1>>}, {<<3,"t2",1>>}, [op |-> "get", id |-> 3], NoReply>>, (* CompanyAddsAPack (7775225985864) *)
    <<{<<1,"t1",1>>}, <<1,"t1",1>>, {3}, {<<1,"t1",1>>,<<3,"t2",1>>}, {}, NoRequest, [op |-> "get", pack |-> <<3,"t2",1>>]>>, (* ServerHandlesGetRequest (7775226046041) *)
    <<{<<1,"t1",1>>,<<3,"t2",1>>}, <<1,"t1",1>>, {3}, {<<1,"t1",1>>,<<3,"t2",1>>}, {}, NoRequest, NoReply>>, (* DeviceReceivesGetReply (7775226480733) *)
    <<{<<1,"t1",1>>,<<3,"t2",1>>}, <<1,"t1",1>>, {3}, {<<1,"t1",1>>,<<3,"t2",1>>}, {<<4,"t2",2>>}, NoRequest, NoReply>>, (* CompanyAddsAPack (7776226346100) *)
    <<{<<1,"t1",1>>,<<3,"t2",1>>}, <<1,"t1",1>>, {3}, {<<1,"t1",1>>,<<3,"t2",1>>}, {<<4,"t2",2>>}, [op |-> "list"], NoReply>>, (* DeviceSendsListRequest (7776226622518) *)
    <<{<<1,"t1",1>>,<<3,"t2",1>>}, <<1,"t1",1>>, {3}, {<<1,"t1",1>>,<<3,"t2",1>>}, {<<4,"t2",2>>}, NoRequest, [op |-> "list", ids |-> {4}]>>, (* ServerHandlesListRequest (7776226957084) *)
    <<{<<1,"t1",1>>,<<3,"t2",1>>}, <<1,"t1",1>>, {3,4}, {<<1,"t1",1>>,<<3,"t2",1>>}, {<<4,"t2",2>>}, NoRequest, NoReply>>, (* DeviceReceivesListReply (7776227244980) *)
    <<{<<1,"t1",1>>,<<3,"t2",1>>}, <<1,"t1",1>>, {3,4}, {<<1,"t1",1>>,<<3,"t2",1>>}, {<<4,"t2",2>>}, [op |-> "get", id |-> 4], NoReply>>, (* DeviceSendsGetRequest (7776227278575) *)
    <<{<<1,"t1",1>>,<<3,"t2",1>>}, <<1,"t1",1>>, {3,4}, {<<1,"t1",1>>,<<3,"t2",1>>}, {<<4,"t2",2>>}, [op |-> "get", id |-> 4], NoReply>>, (* CompanyAddsAPack (7777227317955) *)
    <<{<<1,"t1",1>>,<<3,"t2",1>>}, <<1,"t1",1>>, {3,4}, {<<1,"t1",1>>,<<3,"t2",1>>,<<4,"t2",2>>}, {}, NoRequest, [op |-> "get", pack |-> <<4,"t2",2>>]>>, (* ServerHandlesGetRequest (7777227368796) *)
    <<{<<1,"t1",1>>,<<3,"t2",1>>,<<4,"t2",2>>}, <<1,"t1",1>>, {3,4}, {<<1,"t1",1>>,<<3,"t2",1>>,<<4,"t2",2>>}, {}, NoRequest, NoReply>>, (* DeviceReceivesGetReply (7777227778783) *)
    <<{<<1,"t1",1>>,<<3,"t2",1>>,<<4,"t2",2>>}, <<1,"t1",1>>, {3,4}, {<<1,"t1",1>>,<<3,"t2",1>>,<<4,"t2",2>>}, {}, [op |-> "list"], NoReply>>, (* DeviceSendsListRequest (7778227983125) *)
    <<{<<1,"t1",1>>,<<3,"t2",1>>,<<4,"t2",2>>}, <<1,"t1",1>>, {3,4}, {<<1,"t1",1>>,<<3,"t2",1>>,<<4,"t2",2>>}, {}, NoRequest, [op |-> "list", ids |-> {}]>>, (* ServerHandlesListRequest (7778228303453) *)
    <<{<<1,"t1",1>>,<<3,"t2",1>>,<<4,"t2",2>>}, <<1,"t1",1>>, {3,4}, {<<1,"t1",1>>,<<3,"t2",1>>,<<4,"t2",2>>}, {}, NoRequest, NoReply>> (* DeviceReceivesListReply (7778228602438) *)
  >>
>>

\* Change this to validate another trace.
Trace == Traces[2]

Init ==
  /\ devicePacks = Trace[1][1]
  /\ selectedPack = Trace[1][2]
  /\ knownIds = Trace[1][3]
  /\ serverPacks = Trace[1][4]
  /\ serverUnsentPacks = Trace[1][5]
  /\ request = Trace[1][6]
  /\ reply = Trace[1][7]
  /\ i = 1

Next ==
  /\ i < Len(Trace)
  /\ devicePacks' = Trace[i + 1][1]
  /\ selectedPack' = Trace[i + 1][2]
  /\ knownIds' = Trace[i + 1][3]
  /\ serverPacks' = Trace[i + 1][4]
  /\ serverUnsentPacks' = Trace[i + 1][5]
  /\ request' = Trace[i + 1][6]
  /\ reply' = Trace[i + 1][7]
  /\ i' = i + 1

Spec ==
  /\ Init
  /\ [][Next]_vars
-----------------------------------------------------------------------------
Theme3 == INSTANCE Theme3
=============================================================================
