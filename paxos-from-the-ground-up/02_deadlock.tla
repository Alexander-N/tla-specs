\* http://imnaseer.net/paxos-from-the-ground-up.html?section=3&slide=8
---- MODULE 02_deadlock ----
EXTENDS TLC, Sequences, Integers
CONSTANTS
  Acceptors,
  Proposers,
  Capacity,
  Null

VARIABLES
  acceptorValues,
  inboxes,
  receivedMsgs,
  promises

m == INSTANCE messaging

vars == <<acceptorValues, inboxes, receivedMsgs, promises>>
vars_no_inboxes == <<acceptorValues, receivedMsgs, promises>>

Init ==
  /\ m!Init(Acceptors)
  /\ acceptorValues = [a \in Acceptors |-> Null]
  \* When an acceptor promises to not accept other proposals, the proposal is
  \* saved here.
  /\ promises = [a \in Acceptors |-> Null]

Propose(proposer) ==
  LET sequenceNumber == 1 IN
  LET proposal == <<sequenceNumber, proposer>> IN
  LET promiseMsg == <<"promise", proposal>> IN
  LET acceptMsg == <<"accept", proposal>> IN
  \/ \E a \in Acceptors: ~m!HasMessageReceived(a, promiseMsg)
    /\ acceptorValues[a] = Null
    /\ m!Send(a, promiseMsg)
    /\ UNCHANGED vars_no_inboxes
  \/ \E a \in Acceptors: m!HasMessageReceived(a, promiseMsg)
    /\ acceptorValues[a] = Null
    /\ \A acp \in Acceptors: m!HasMessageReceived(acp, promiseMsg)
    /\ m!Send(a, acceptMsg)
    /\ UNCHANGED vars_no_inboxes

AcceptMsg(acceptor, msg) ==
  acceptorValues' = [acceptorValues EXCEPT ![acceptor] = msg]

Promise(acceptor, msg) ==
  promises' = [promises EXCEPT ![acceptor] = msg]

Accept(acceptor) ==
  \E msg \in m!Receive(acceptor):
    LET messageType == Head(msg) IN
    LET proposal == Tail(msg) IN
    LET nothingPromised == promises[acceptor] = Null IN
    LET alreadyPromised == ~nothingPromised IN
    LET promisedThisValue == promises[acceptor] = proposal IN
    \/
      /\ messageType = "promise" /\ nothingPromised
      /\ Promise(acceptor, proposal)
      /\ m!AckMsg(acceptor)
      /\ UNCHANGED <<acceptorValues>>
    \/ messageType = "accept" /\ promisedThisValue
      /\ AcceptMsg(acceptor, msg)
      /\ m!AckMsg(acceptor)
      /\ UNCHANGED <<promises>>
    \/
      /\
        \/ messageType = "promise" /\ alreadyPromised
        \/ messageType = "accept" /\ ~promisedThisValue
      /\ m!RemoveMsg(acceptor)
      /\ UNCHANGED vars_no_inboxes

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
NoValuesNull == \A v \in Range(acceptorValues): v /= Null
EventuallyConsistent == <>[](AllValuesEqual /\ NoValuesNull)
====
