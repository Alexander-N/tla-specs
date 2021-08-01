---- MODULE messagingPlusCal ----
EXTENDS TLC, Sequences, Integers
CONSTANTS Capacity
VARIABLES
  inboxes,
  receivedMsgs

Init(nodes) ==
  /\ inboxes = [n \in nodes |-> <<>>]
  /\ receivedMsgs = {}

Send(receiver, payload) ==
  LET inbox == inboxes[receiver] IN
  /\ Len(inbox) < Capacity
  /\ inboxes' = [inboxes EXCEPT ![receiver] = Append(inbox, payload)]

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
  /\ receivedMsgs' = receivedMsgs \union {[payload |-> msg, dest |-> receiver]}

HasMessageReceived(receiver, msg) ==
  [payload |-> msg, dest |-> receiver] \in receivedMsgs
====
