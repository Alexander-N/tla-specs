\* http://imnaseer.net/paxos-from-the-ground-up.html?section=3&slide=2
---- MODULE 01_race ----
EXTENDS TLC, Sequences, Integers
CONSTANTS
  Acceptors,
  Proposers,
  Capacity,
  Null

VARIABLES
  acceptorValues,
  inboxes,
  receivedMsgs

m == INSTANCE messaging

vars == <<acceptorValues, inboxes, receivedMsgs>>

Init ==
  /\ m!Init(Acceptors)
  /\ acceptorValues = [a \in Acceptors |-> Null]

Propose(proposer) ==
  LET msg == proposer IN
  \E a \in Acceptors:
    /\ ~m!HasMessageReceived(a, msg)
    /\ m!Send(a, msg)
    /\ UNCHANGED <<acceptorValues, receivedMsgs>>

AcceptMsg(acceptor, msg) ==
  acceptorValues' = [acceptorValues EXCEPT ![acceptor] = msg]

Accept(acceptor) ==
  \E msg \in m!Receive(acceptor):
    /\ AcceptMsg(acceptor, msg)
    /\ m!AckMsg(acceptor)

Terminating ==
  /\ \A node \in DOMAIN inboxes: Len(inboxes[node]) = 0
  /\ UNCHANGED vars

Next ==
  \/ \E p \in Proposers: Propose(p)
  \/ \E a \in Acceptors: Accept(a)
  \/ Terminating

Spec == Init /\ [][Next]_vars

Range(f) == {f[x] : x \in DOMAIN f}
AllValuesEqual == \A v1, v2 \in Range(acceptorValues): v1 = v2
EventuallyConsistent == <>[]AllValuesEqual
====
