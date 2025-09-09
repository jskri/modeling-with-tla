---------------------------- MODULE ThemeCommon2 ----------------------------
EXTENDS ThemeCommon1, Functions
CONSTANTS Id, PackId, PackFromId, NewPack(_),
  Request, Reply, NoRequest, NoReply

ASSUME Assumptions2 ==
  /\ Assumptions
  /\ PackId \in [Pack -> Id]
  /\ PackFromId \in [Id -> Pack]
  /\ \A reply \in (Reply \union {NoReply}) :
       NewPack(reply) = IF reply \in [op : {"get"}, pack : Pack]
                        THEN reply.pack
                        ELSE NoPack
  /\ NoRequest \notin Request
  /\ NoReply \notin Reply
  /\ Request = [op : {"list"}] \union [op : {"get"}, id : Id]
  /\ Reply = [op : {"list"}, ids : SUBSET Id] \union [op : {"get"}, pack : Pack]
=============================================================================