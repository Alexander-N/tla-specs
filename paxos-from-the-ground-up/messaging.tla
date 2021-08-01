---- MODULE messaging ----
EXTENDS TLC, Sequences, Integers
CONSTANTS Capacity
VARIABLES
  inboxes,
  acceptedMsgs,
  rejectedMsgs


Init(nodes) ==
  /\ inboxes = [n \in nodes |-> <<>>]
  /\ acceptedMsgs = {}
  /\ rejectedMsgs = {}

receivedMsgs == acceptedMsgs \union rejectedMsgs

Send(receiver, payload) ==
  LET inbox == inboxes[receiver] IN
  /\ Len(inbox) < Capacity
  /\ inboxes' = [inboxes EXCEPT ![receiver] = Append(inbox, payload)]
  /\ UNCHANGED <<acceptedMsgs, rejectedMsgs>>

Receive(receiver) ==
  LET inbox == inboxes[receiver] IN
  IF Len(inbox) = 0
  THEN {}
  ELSE {Head(inbox)}

RemoveMsg(receiver) ==
  inboxes' = [inboxes EXCEPT ![receiver] = Tail(inboxes[receiver])]

AckMsg(receiver) ==
  LET inbox == inboxes[receiver] IN
  LET msg == Head(inbox) IN
  /\ RemoveMsg(receiver)
  /\ acceptedMsgs' = acceptedMsgs \union {[payload |-> msg, dest |-> receiver]}
  /\ UNCHANGED rejectedMsgs

RejectMsg(receiver) ==
  LET inbox == inboxes[receiver] IN
  LET msg == Head(inbox) IN
  /\ RemoveMsg(receiver)
  /\ rejectedMsgs' = rejectedMsgs \union {[payload |-> msg, dest |-> receiver]}
  /\ UNCHANGED acceptedMsgs

HasMessageReceived(receiver, msg) ==
  [payload |-> msg, dest |-> receiver] \in receivedMsgs

HasMessageAccepted(receiver, msg) ==
  [payload |-> msg, dest |-> receiver] \in acceptedMsgs

HasMessageRejected(receiver, msg) ==
  [payload |-> msg, dest |-> receiver] \in rejectedMsgs
====
