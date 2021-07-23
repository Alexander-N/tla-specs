\* http://imnaseer.net/paxos-from-the-ground-up.html?section=3&slide=2
---- MODULE 01_race_pluscal ----
EXTENDS TLC, Sequences, Integers
CONSTANTS
  Acceptors,
  Proposers,
  Capacity,
  Null

(*--algorithm 01_race_pluscal

variables
  inboxes = [a \in Acceptors |-> <<>>],
  receivedMsgs = {},

define
  m == INSTANCE messaging
end define;

macro Send(receiver, payload) begin
  with inbox = inboxes[receiver] do
    await Len(inbox) < Capacity;
    inboxes[receiver] := Append(inbox, payload);
  end with;
end macro;

macro AckMsg(receiver) begin
  with
    inbox = inboxes[receiver],
    ackMsg = Head(inbox) do
    inboxes[receiver] := Tail(inbox);
    receivedMsgs := receivedMsgs \union {[payload |-> ackMsg, dest |-> receiver]}
  end with;
end macro;

fair process proposer \in Proposers
begin
  p1: while TRUE do
    with a \in Acceptors do
      await ~m!HasMessageReceived(a, self);
      Send(a, self);
    end with;
  end while;
end process;

fair process acceptor \in Acceptors
variables acceptorValue = Null;
begin
  a1: while TRUE do
    with msg \in m!Receive(self) do
      acceptorValue := msg;
    end with;
    AckMsg(self);
  end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "2176eb7a" /\ chksum(tla) = "86984997")
VARIABLES inboxes, receivedMsgs

(* define statement *)
m == INSTANCE messaging

VARIABLE acceptorValue

vars == << inboxes, receivedMsgs, acceptorValue >>

ProcSet == (Proposers) \cup (Acceptors)

Init == (* Global variables *)
        /\ inboxes = [a \in Acceptors |-> <<>>]
        /\ receivedMsgs = {}
        (* Process acceptor *)
        /\ acceptorValue = [self \in Acceptors |-> Null]

proposer(self) == /\ \E a \in Acceptors:
                       /\ ~m!HasMessageReceived(a, self)
                       /\ LET inbox == inboxes[a] IN
                            /\ Len(inbox) < Capacity
                            /\ inboxes' = [inboxes EXCEPT ![a] = Append(inbox, self)]
                  /\ UNCHANGED << receivedMsgs, acceptorValue >>

acceptor(self) == /\ \E msg \in m!Receive(self):
                       acceptorValue' = [acceptorValue EXCEPT ![self] = msg]
                  /\ LET inbox == inboxes[self] IN
                       LET ackMsg == Head(inbox) IN
                         /\ inboxes' = [inboxes EXCEPT ![self] = Tail(inbox)]
                         /\ receivedMsgs' = (receivedMsgs \union {[payload |-> ackMsg, dest |-> self]})

Next == (\E self \in Proposers: proposer(self))
           \/ (\E self \in Acceptors: acceptor(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Proposers : WF_vars(proposer(self))
        /\ \A self \in Acceptors : WF_vars(acceptor(self))

\* END TRANSLATION

Terminating ==
  /\ \A node \in DOMAIN inboxes: Len(inboxes[node]) = 0
  /\ UNCHANGED vars
\* Spec with termination
NextT == Next \/ Terminating
SpecT == Init /\ [][NextT]_vars

Range(f) == {f[x] : x \in DOMAIN f}
AllValuesEqual == \A v1, v2 \in Range(acceptorValue): v1 = v2
EventuallyConsistent == <>[]AllValuesEqual
====
