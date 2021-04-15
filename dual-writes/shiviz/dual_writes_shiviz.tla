---- MODULE dual_writes_shiviz ----
EXTENDS TLC, Integers, ShiViz
CONSTANTS Clients, Database, Cache, Null

Storages == {Database, Cache}

(*--algorithm dual_writes
variables
  MessageDB = Null;
  MessageCache = Null;
  ValueDB = Null;
  ValueCache = Null;

fair process client \in Clients
begin
  SendDatabase:
    await MessageDB = Null;
    MessageDB := self;
  AckDatabase:
    await MessageDB = Null;
  SendCache:
    await MessageCache = Null;
    MessageCache := self;
  AckCache:
    await MessageCache = Null;
end process;

fair process database = Database
begin
  ReceiveDatabase1:
    await MessageDB /= Null;
    ValueDB := MessageDB;
    MessageDB := Null;
  ReceiveDatabase2:
    await MessageDB /= Null;
    ValueDB := MessageDB;
    MessageDB := Null;
end process;

fair process cache = Cache
begin
  ReceiveCache1:
    await MessageCache /= Null;
    ValueCache := MessageCache;
    MessageCache := Null;
  ReceiveCache:
    await MessageCache /= Null;
    ValueCache := MessageCache;
    MessageCache := Null;
end process;


end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "f935bb6e" /\ chksum(tla) = "cc58fc83")
VARIABLES MessageDB, MessageCache, ValueDB, ValueCache, pc

vars == << MessageDB, MessageCache, ValueDB, ValueCache, pc >>

ProcSet == (Clients) \cup {Database} \cup {Cache}

Init == (* Global variables *)
        /\ MessageDB = Null
        /\ MessageCache = Null
        /\ ValueDB = Null
        /\ ValueCache = Null
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "SendDatabase"
                                        [] self = Database -> "ReceiveDatabase1"
                                        [] self = Cache -> "ReceiveCache1"]

SendDatabase(self) == /\ pc[self] = "SendDatabase"
                      /\ MessageDB = Null
                      /\ MessageDB' = self
                      /\ pc' = [pc EXCEPT ![self] = "AckDatabase"]
                      /\ UNCHANGED << MessageCache, ValueDB, ValueCache >>

AckDatabase(self) == /\ pc[self] = "AckDatabase"
                     /\ MessageDB = Null
                     /\ pc' = [pc EXCEPT ![self] = "SendCache"]
                     /\ UNCHANGED << MessageDB, MessageCache, ValueDB, 
                                     ValueCache >>

SendCache(self) == /\ pc[self] = "SendCache"
                   /\ MessageCache = Null
                   /\ MessageCache' = self
                   /\ pc' = [pc EXCEPT ![self] = "AckCache"]
                   /\ UNCHANGED << MessageDB, ValueDB, ValueCache >>

AckCache(self) == /\ pc[self] = "AckCache"
                  /\ MessageCache = Null
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << MessageDB, MessageCache, ValueDB, ValueCache >>

client(self) == SendDatabase(self) \/ AckDatabase(self) \/ SendCache(self)
                   \/ AckCache(self)

ReceiveDatabase1 == /\ pc[Database] = "ReceiveDatabase1"
                    /\ MessageDB /= Null
                    /\ ValueDB' = MessageDB
                    /\ MessageDB' = Null
                    /\ pc' = [pc EXCEPT ![Database] = "ReceiveDatabase2"]
                    /\ UNCHANGED << MessageCache, ValueCache >>

ReceiveDatabase2 == /\ pc[Database] = "ReceiveDatabase2"
                    /\ MessageDB /= Null
                    /\ ValueDB' = MessageDB
                    /\ MessageDB' = Null
                    /\ pc' = [pc EXCEPT ![Database] = "Done"]
                    /\ UNCHANGED << MessageCache, ValueCache >>

database == ReceiveDatabase1 \/ ReceiveDatabase2

ReceiveCache1 == /\ pc[Cache] = "ReceiveCache1"
                 /\ MessageCache /= Null
                 /\ ValueCache' = MessageCache
                 /\ MessageCache' = Null
                 /\ pc' = [pc EXCEPT ![Cache] = "ReceiveCache"]
                 /\ UNCHANGED << MessageDB, ValueDB >>

ReceiveCache == /\ pc[Cache] = "ReceiveCache"
                /\ MessageCache /= Null
                /\ ValueCache' = MessageCache
                /\ MessageCache' = Null
                /\ pc' = [pc EXCEPT ![Cache] = "Done"]
                /\ UNCHANGED << MessageDB, ValueDB >>

cache == ReceiveCache1 \/ ReceiveCache

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == database \/ cache
           \/ (\E self \in Clients: client(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : WF_vars(client(self))
        /\ WF_vars(database)
        /\ WF_vars(cache)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

EventuallyConsistent == <>[](ValueCache = ValueDB)
====
