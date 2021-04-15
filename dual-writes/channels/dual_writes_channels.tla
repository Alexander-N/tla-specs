---- MODULE dual_writes_channels ----
EXTENDS TLC, Integers, FiniteSets

INSTANCE ChannelsReliable

CONSTANTS ClientA, ClientB, Database, Cache, Null, Ack

Clients == {ClientA, ClientB}
Storages == {Database, Cache}
Msg == (ClientA :> "A") @@ (ClientB :> "B")

(*--algorithm dual_writes_channels
variables
  C = InitChannels(Clients \union Storages);

\* Send(channels, sender, receiver, msg, msgLabel, senderState)
\* MarkMessageReceived(C, receiver, msg, receiverState)
fair process client \in Clients
  begin
    SendDatabase:
      C := Send(C, self, Database, Msg[self], Msg[self], "");
    GetAckDatabase:
      await HasMessage(C, self);
      with wrappedMsg \in NextMessages(C, self) do
        assert wrappedMsg.rawMsg.payload = Ack /\ wrappedMsg.rawMsg.sender = Database;
        C := MarkMessageReceived(C, self, wrappedMsg, "");
      end with;
    SendCache:
      C := Send(C, self, Cache, Msg[self], Msg[self], "");
    GetAckCache:
      await HasMessage(C, self);
      with wrappedMsg \in NextMessages(C, self) do
        assert wrappedMsg.rawMsg.payload = Ack /\ wrappedMsg.rawMsg.sender = Cache;
        C := MarkMessageReceived(C, self, wrappedMsg, "");
      end with;
end process;

fair process storage \in Storages
variables
  sender = Null;
  \* The storage holds one single value in this variable
  value = Null;
  \* Counter for received messages
  received = 0;
begin
  Receive:
    await HasMessage(C, self);
    with wrappedMsg \in NextMessages(C, self) do
      value := wrappedMsg.rawMsg.payload;
      C := MarkMessageReceived(C, self, wrappedMsg, value);
      sender := wrappedMsg.rawMsg.sender;
    end with;
    received := received + 1;
  SendAck:
    C := Send(C, self, sender, Ack, "Ack", value);
    \* Only receive two messages, then terminate.
    if received < 2 then
      \* "while" would need another label so use goto instead to not spam the
      \* error trace :-)
      goto Receive
    end if;
end process;


end algorithm;*)

\* BEGIN TRANSLATION (chksum(pcal) = "8e437a" /\ chksum(tla) = "cccd43bc")
VARIABLES C, pc, sender, value, received

vars == << C, pc, sender, value, received >>

ProcSet == (Clients) \cup (Storages)

Init == (* Global variables *)
        /\ C = InitChannels(Clients \union Storages)
        (* Process storage *)
        /\ sender = [self \in Storages |-> Null]
        /\ value = [self \in Storages |-> Null]
        /\ received = [self \in Storages |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "SendDatabase"
                                        [] self \in Storages -> "Receive"]

SendDatabase(self) == /\ pc[self] = "SendDatabase"
                      /\ C' = Send(C, self, Database, Msg[self], Msg[self], "")
                      /\ pc' = [pc EXCEPT ![self] = "GetAckDatabase"]
                      /\ UNCHANGED << sender, value, received >>

GetAckDatabase(self) == /\ pc[self] = "GetAckDatabase"
                        /\ HasMessage(C, self)
                        /\ \E wrappedMsg \in NextMessages(C, self):
                             /\ Assert(wrappedMsg.rawMsg.payload = Ack /\ wrappedMsg.rawMsg.sender = Database, 
                                       "Failure of assertion at line 25, column 9.")
                             /\ C' = MarkMessageReceived(C, self, wrappedMsg, "")
                        /\ pc' = [pc EXCEPT ![self] = "SendCache"]
                        /\ UNCHANGED << sender, value, received >>

SendCache(self) == /\ pc[self] = "SendCache"
                   /\ C' = Send(C, self, Cache, Msg[self], Msg[self], "")
                   /\ pc' = [pc EXCEPT ![self] = "GetAckCache"]
                   /\ UNCHANGED << sender, value, received >>

GetAckCache(self) == /\ pc[self] = "GetAckCache"
                     /\ HasMessage(C, self)
                     /\ \E wrappedMsg \in NextMessages(C, self):
                          /\ Assert(wrappedMsg.rawMsg.payload = Ack /\ wrappedMsg.rawMsg.sender = Cache, 
                                    "Failure of assertion at line 33, column 9.")
                          /\ C' = MarkMessageReceived(C, self, wrappedMsg, "")
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << sender, value, received >>

client(self) == SendDatabase(self) \/ GetAckDatabase(self)
                   \/ SendCache(self) \/ GetAckCache(self)

Receive(self) == /\ pc[self] = "Receive"
                 /\ HasMessage(C, self)
                 /\ \E wrappedMsg \in NextMessages(C, self):
                      /\ value' = [value EXCEPT ![self] = wrappedMsg.rawMsg.payload]
                      /\ C' = MarkMessageReceived(C, self, wrappedMsg, value'[self])
                      /\ sender' = [sender EXCEPT ![self] = wrappedMsg.rawMsg.sender]
                 /\ received' = [received EXCEPT ![self] = received[self] + 1]
                 /\ pc' = [pc EXCEPT ![self] = "SendAck"]

SendAck(self) == /\ pc[self] = "SendAck"
                 /\ C' = Send(C, self, sender[self], Ack, "Ack", value[self])
                 /\ IF received[self] < 2
                       THEN /\ pc' = [pc EXCEPT ![self] = "Receive"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << sender, value, received >>

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
