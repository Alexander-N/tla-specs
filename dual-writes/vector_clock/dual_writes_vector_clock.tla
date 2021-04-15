---- MODULE dual_writes_vector_clock ----
EXTENDS TLC, Integers, Sequences, Json
CONSTANTS Clients, Database, Cache, Null, Ack

Storages == {Database, Cache}

(*--algorithm dual_writes
variables
  Messages = [host \in Storages \union Clients |-> <<>>];
  \* ShiViz Variables
  VectorClock = [host \in Clients \union Storages |-> 0];
  Host = Null;
  Event = Null;

define
  max(a, b) == IF a >= b THEN a ELSE b

  merge(clockA, clockB) == [
    \* DOMAIN of clockA and clockB has to be the same
    host \in DOMAIN clockA \union DOMAIN clockB |-> max(clockA[host], clockB[host])
  ]

  inc(clock, host) == [clock EXCEPT ![host] = clock[host] + 1]
end define;

macro send(destination, source, clock, value) begin
  clock := inc(clock, source);

  Messages[destination] := Append(
    Messages[destination],
    [
      destination |-> destination,
      source |-> source,
      clock |-> clock,
      value |-> value
  ]);

  \* Variables for Shiviz
  Host := source;
  Event := pc[Host];
  VectorClock := ToJsonObject(clock);
end macro;

macro receive(destination, clock) begin
  await Len(Messages[destination]) > 0;
  receivedMessage := Head(Messages[destination]);
  Messages[self] := Tail(Messages[self]);

  clock := merge(inc(clock, destination), receivedMessage.clock);

  \* Variables for Shiviz
  Host := destination;
  Event := pc[Host];
  VectorClock := ToJsonObject(clock);
end macro;

fair process client \in Clients
variables
  \* Return value for receive
  receivedMessage = Null;
  localVectorClock = [host \in Clients \union Storages |-> 0];
begin
  SendDatabase:
    send(Database, self, localVectorClock, self);
  GetAckDatabase:
    receive(self, localVectorClock);
    assert receivedMessage.value = Ack /\ receivedMessage.source = Database;
  SendCache:
    send(Cache, self, localVectorClock, self);
  GetAckCache:
    receive(self, localVectorClock);
    assert receivedMessage.value = Ack /\ receivedMessage.source = Cache;
end process;

fair process storage \in Storages
variables
  \* The storage holds one single value in this variable
  value = Null;
  \* Counter for received messages
  received = 0;
  \* Return value for receive
  receivedMessage = Null;
  localVectorClock = [host \in Clients \union Storages |-> 0];
begin
  Receive:
    receive(self, localVectorClock);
    value := receivedMessage.value;
    received := received + 1;
  SendAck:
    send(receivedMessage.source, self, localVectorClock, Ack);
    \* Only receive two messages, then terminate.
    if received < 2 then
      \* "while" would need another label so use goto instead to not spam the
      \* error trace :-)
      goto Receive
    end if;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "584e2494" /\ chksum(tla) = "4f496dd4")
\* Process variable receivedMessage of process client at line 60 col 3 changed to receivedMessage_
\* Process variable localVectorClock of process client at line 61 col 3 changed to localVectorClock_
VARIABLES Messages, VectorClock, Host, Event, pc

(* define statement *)
max(a, b) == IF a >= b THEN a ELSE b

merge(clockA, clockB) == [

  host \in DOMAIN clockA \union DOMAIN clockB |-> max(clockA[host], clockB[host])
]

inc(clock, host) == [clock EXCEPT ![host] = clock[host] + 1]

VARIABLES receivedMessage_, localVectorClock_, value, received, 
          receivedMessage, localVectorClock

vars == << Messages, VectorClock, Host, Event, pc, receivedMessage_, 
           localVectorClock_, value, received, receivedMessage, 
           localVectorClock >>

ProcSet == (Clients) \cup (Storages)

Init == (* Global variables *)
        /\ Messages = [host \in Storages \union Clients |-> <<>>]
        /\ VectorClock = [host \in Clients \union Storages |-> 0]
        /\ Host = Null
        /\ Event = Null
        (* Process client *)
        /\ receivedMessage_ = [self \in Clients |-> Null]
        /\ localVectorClock_ = [self \in Clients |-> [host \in Clients \union Storages |-> 0]]
        (* Process storage *)
        /\ value = [self \in Storages |-> Null]
        /\ received = [self \in Storages |-> 0]
        /\ receivedMessage = [self \in Storages |-> Null]
        /\ localVectorClock = [self \in Storages |-> [host \in Clients \union Storages |-> 0]]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "SendDatabase"
                                        [] self \in Storages -> "Receive"]

SendDatabase(self) == /\ pc[self] = "SendDatabase"
                      /\ localVectorClock_' = [localVectorClock_ EXCEPT ![self] = inc(localVectorClock_[self], self)]
                      /\ Messages' = [Messages EXCEPT ![Database] =                          Append(
                                                                      Messages[Database],
                                                                      [
                                                                        destination |-> Database,
                                                                        source |-> self,
                                                                        clock |-> localVectorClock_'[self],
                                                                        value |-> self
                                                                    ])]
                      /\ Host' = self
                      /\ Event' = pc[Host']
                      /\ VectorClock' = ToJsonObject(localVectorClock_'[self])
                      /\ pc' = [pc EXCEPT ![self] = "GetAckDatabase"]
                      /\ UNCHANGED << receivedMessage_, value, received, 
                                      receivedMessage, localVectorClock >>

GetAckDatabase(self) == /\ pc[self] = "GetAckDatabase"
                        /\ Len(Messages[self]) > 0
                        /\ receivedMessage_' = [receivedMessage_ EXCEPT ![self] = Head(Messages[self])]
                        /\ Messages' = [Messages EXCEPT ![self] = Tail(Messages[self])]
                        /\ localVectorClock_' = [localVectorClock_ EXCEPT ![self] = merge(inc(localVectorClock_[self], self), receivedMessage_'[self].clock)]
                        /\ Host' = self
                        /\ Event' = pc[Host']
                        /\ VectorClock' = ToJsonObject(localVectorClock_'[self])
                        /\ Assert(receivedMessage_'[self].value = Ack /\ receivedMessage_'[self].source = Database, 
                                  "Failure of assertion at line 67, column 5.")
                        /\ pc' = [pc EXCEPT ![self] = "SendCache"]
                        /\ UNCHANGED << value, received, receivedMessage, 
                                        localVectorClock >>

SendCache(self) == /\ pc[self] = "SendCache"
                   /\ localVectorClock_' = [localVectorClock_ EXCEPT ![self] = inc(localVectorClock_[self], self)]
                   /\ Messages' = [Messages EXCEPT ![Cache] =                          Append(
                                                                Messages[Cache],
                                                                [
                                                                  destination |-> Cache,
                                                                  source |-> self,
                                                                  clock |-> localVectorClock_'[self],
                                                                  value |-> self
                                                              ])]
                   /\ Host' = self
                   /\ Event' = pc[Host']
                   /\ VectorClock' = ToJsonObject(localVectorClock_'[self])
                   /\ pc' = [pc EXCEPT ![self] = "GetAckCache"]
                   /\ UNCHANGED << receivedMessage_, value, received, 
                                   receivedMessage, localVectorClock >>

GetAckCache(self) == /\ pc[self] = "GetAckCache"
                     /\ Len(Messages[self]) > 0
                     /\ receivedMessage_' = [receivedMessage_ EXCEPT ![self] = Head(Messages[self])]
                     /\ Messages' = [Messages EXCEPT ![self] = Tail(Messages[self])]
                     /\ localVectorClock_' = [localVectorClock_ EXCEPT ![self] = merge(inc(localVectorClock_[self], self), receivedMessage_'[self].clock)]
                     /\ Host' = self
                     /\ Event' = pc[Host']
                     /\ VectorClock' = ToJsonObject(localVectorClock_'[self])
                     /\ Assert(receivedMessage_'[self].value = Ack /\ receivedMessage_'[self].source = Cache, 
                               "Failure of assertion at line 72, column 5.")
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << value, received, receivedMessage, 
                                     localVectorClock >>

client(self) == SendDatabase(self) \/ GetAckDatabase(self)
                   \/ SendCache(self) \/ GetAckCache(self)

Receive(self) == /\ pc[self] = "Receive"
                 /\ Len(Messages[self]) > 0
                 /\ receivedMessage' = [receivedMessage EXCEPT ![self] = Head(Messages[self])]
                 /\ Messages' = [Messages EXCEPT ![self] = Tail(Messages[self])]
                 /\ localVectorClock' = [localVectorClock EXCEPT ![self] = merge(inc(localVectorClock[self], self), receivedMessage'[self].clock)]
                 /\ Host' = self
                 /\ Event' = pc[Host']
                 /\ VectorClock' = ToJsonObject(localVectorClock'[self])
                 /\ value' = [value EXCEPT ![self] = receivedMessage'[self].value]
                 /\ received' = [received EXCEPT ![self] = received[self] + 1]
                 /\ pc' = [pc EXCEPT ![self] = "SendAck"]
                 /\ UNCHANGED << receivedMessage_, localVectorClock_ >>

SendAck(self) == /\ pc[self] = "SendAck"
                 /\ localVectorClock' = [localVectorClock EXCEPT ![self] = inc(localVectorClock[self], self)]
                 /\ Messages' = [Messages EXCEPT ![(receivedMessage[self].source)] =                          Append(
                                                                                       Messages[(receivedMessage[self].source)],
                                                                                       [
                                                                                         destination |-> (receivedMessage[self].source),
                                                                                         source |-> self,
                                                                                         clock |-> localVectorClock'[self],
                                                                                         value |-> Ack
                                                                                     ])]
                 /\ Host' = self
                 /\ Event' = pc[Host']
                 /\ VectorClock' = ToJsonObject(localVectorClock'[self])
                 /\ IF received[self] < 2
                       THEN /\ pc' = [pc EXCEPT ![self] = "Receive"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << receivedMessage_, localVectorClock_, value, 
                                 received, receivedMessage >>

storage(self) == Receive(self) \/ SendAck(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Clients: client(self))
           \/ (\E self \in Storages: storage(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : WF_vars(client(self))
        /\ \A self \in Storages : WF_vars(storage(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

AllValuesEqual ==
  \A s1, s2 \in Storages:
    value[s1] = value[s2]
EventuallyConsistent == <>[]AllValuesEqual

====
