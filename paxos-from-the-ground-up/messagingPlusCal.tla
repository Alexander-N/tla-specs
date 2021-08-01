---- MODULE messagingPlusCal ----
EXTENDS TLC, Sequences, Integers
CONSTANTS Capacity
VARIABLES
  inboxes,
  receivedMsgs

Init(nodes) ==
  /\ inboxes = [n \in nodes |-> <<>>]
  /\ receivedMsgs = {}

Receive(receiver) ==
  LET inbox == inboxes[receiver] IN
  IF Len(inbox) = 0
  THEN {}
  ELSE {Head(inbox)}

HasMessageReceived(receiver, msg) ==
  [payload |-> msg, dest |-> receiver] \in receivedMsgs
====
