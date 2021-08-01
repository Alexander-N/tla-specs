\* http://imnaseer.net/paxos-from-the-ground-up.html?section=3&slide=22
---- MODULE 03_deadlock ----
EXTENDS TLC, Sequences, Integers, SequencesExt
CONSTANTS
  Acceptors,
  Proposers,
  Capacity,
  Null

VARIABLES
  acceptorValues,
  inboxes,
  acceptedMsgs,
  rejectedMsgs,
  promises

m == INSTANCE messaging

vars == <<acceptorValues, inboxes, promises, acceptedMsgs, rejectedMsgs>>

GetIndex(element, sequence) ==
  CHOOSE i \in 1..Len(sequence) : sequence[i] = element
proposerSeq == SetToSeq(Proposers)
proposerOrder == [p \in Proposers |-> GetIndex(p, proposerSeq)]
hasPriority(proposal1, proposal2) ==
  IF proposal2 = Null THEN
    TRUE
  ELSE
    LET sequenceNumber1 == proposal1[1] IN
    LET sequenceNumber2 == proposal2[1] IN
    IF sequenceNumber1 /= sequenceNumber2 THEN
      sequenceNumber1 > sequenceNumber2
    ELSE
      LET proposer1 == proposal1[2] IN
      LET proposer2 == proposal2[2] IN
      proposerOrder[proposer1] > proposerOrder[proposer2]

Init ==
  /\ m!Init(Acceptors)
  /\ acceptorValues = [a \in Acceptors |-> Null]
  \* When an acceptor promises to not accept other proposals, the proposal is
  \* saved here.
  /\ promises = [a \in Acceptors |-> Null]

SendPromiseMsg(proposer) ==
  LET sequenceNumber == 1 IN
  LET proposal == <<sequenceNumber, proposer>> IN
  LET promiseMsg == <<"promise", proposal>> IN
  \/ \E a \in Acceptors: ~m!HasMessageAccepted(a, promiseMsg)
    /\ ~m!HasMessageRejected(a, promiseMsg)
    /\ m!Send(a, promiseMsg)
    /\ UNCHANGED <<acceptorValues, promises>>

SendAcceptMsg(proposer) ==
  LET sequenceNumber == 1 IN
  LET proposal == <<sequenceNumber, proposer>> IN
  LET promiseMsg == <<"promise", proposal>> IN
  LET acceptMsg == <<"accept", proposal>> IN
  \/ \E a \in Acceptors: m!HasMessageAccepted(a, promiseMsg)
    /\ ~m!HasMessageReceived(a, acceptMsg)
    /\ \A acp \in Acceptors: m!HasMessageAccepted(acp, promiseMsg)
    /\ m!Send(a, acceptMsg)
    /\ UNCHANGED <<acceptorValues, promises>>

AcceptMsg(acceptor, msg) ==
  acceptorValues' = [acceptorValues EXCEPT ![acceptor] = msg]

SavePromise(acceptor, msg) ==
  promises' = [promises EXCEPT ![acceptor] = msg]

HasAccepted(acceptor) ==
  acceptorValues[acceptor] /= Null

ReceiveMsg(acceptor) ==
  \E msg \in m!Receive(acceptor):
    LET messageType == msg[1] IN
    LET proposal == msg[2] IN
    LET oldProposal == promises[acceptor] IN
    LET newProposalHasPriority == hasPriority(proposal, oldProposal) IN
    LET promisedThis == promises[acceptor] = proposal IN
    \/
      /\ ~HasAccepted(acceptor)
      /\ messageType = "promise"
      /\ newProposalHasPriority
      /\ SavePromise(acceptor, proposal)
      /\ m!AckMsg(acceptor)
      /\ UNCHANGED <<acceptorValues>>
    \/
      /\ ~HasAccepted(acceptor)
      /\ messageType = "accept"
      /\ promisedThis
      /\ AcceptMsg(acceptor, msg)
      /\ m!AckMsg(acceptor)
      /\ UNCHANGED <<promises>>
    \/
      /\
        \/ HasAccepted(acceptor)
        \/ messageType = "promise" /\ ~newProposalHasPriority
        \/ messageType = "accept" /\ ~promisedThis
      /\ m!RejectMsg(acceptor)
      /\ UNCHANGED <<acceptorValues, promises>>

Terminating ==
  /\ \A node \in DOMAIN inboxes: Len(inboxes[node]) = 0
  /\ \A a \in Acceptors: acceptorValues[a] /= Null
  /\ UNCHANGED vars

SendPromise == \E p \in Proposers: SendPromiseMsg(p)
SendAccept == \E p \in Proposers: SendAcceptMsg(p)
Receive == \E a \in Acceptors: ReceiveMsg(a)
Next ==
  \/ SendPromise
  \/ SendAccept
  \/ Receive
  \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Range(f) == {f[x] : x \in DOMAIN f}
AllValuesEqual == \A v1, v2 \in Range(acceptorValues): v1 = v2
EventuallyConsistent == <>[](AllValuesEqual)

NoValuesNull == \A v \in Range(acceptorValues): v /= Null
ValuesGetEventuallySet == <>[]NoValuesNull
====
