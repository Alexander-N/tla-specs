---- MODULE crdt_fixed ----
EXTENDS TLC, FiniteSets, Naturals, Sequences
CONSTANTS MAX_TIMESTAMP, KEYS, VALUES, N_NODES
VARIABLES timestamp, values, deliverQueues

vars == <<timestamp, values, deliverQueues>>
nodeIds == 1..N_NODES

DeliverSet(n, T, t, k, v) ==
  values' = [
      values EXCEPT ![n] = {<<tp, kp, vp>> \in values[n] : tp \notin T} \union { <<t, k, v>> }
    ]

DeliverDelete(n, T) ==
  values' = [
    values EXCEPT ![n] = {<<t, k, v>> \in values[n] : t \notin T}
  ]

Deliver(n, command, payload) ==
  \/ command = "set"
    /\ DeliverSet(n, payload[1], payload[2], payload[3], payload[4])
  \/ command = "delete"
    /\ DeliverDelete(n, payload)

Broadcast(n, command, payload) ==
  /\ Deliver(n, command, payload)
  /\ deliverQueues' = [
      i \in nodeIds |->
        IF i = n THEN
          deliverQueues[i]
        ELSE
          Append(deliverQueues[i], <<command, payload>>)
      ]

RequestSet(n, k, v) ==
  LET matches == {<<t, kp, vp>> \in values[n] : k = kp}  IN
  LET T == {t : <<t, kp, vp>> \in matches}  IN
    /\ timestamp' = timestamp + 1
    /\ Broadcast(n, "set", <<T, timestamp, k, v>>)

RequestDelete(n, k) ==
  LET matches == {<<t, kp, v>> \in values[n] : k = kp}  IN
  LET T == {t : <<t, kp, v>> \in matches}  IN
    /\ T /= {}
    /\ Broadcast(n, "delete", T)

RequestSetOnNode ==
  /\ timestamp < MAX_TIMESTAMP
  /\ \E <<n, k, v>> \in nodeIds \X KEYS \X VALUES : RequestSet(n, k, v)

RequestDeleteOnNode ==
  /\ \E <<n, k>> \in nodeIds \X KEYS : RequestDelete(n, k)
  /\ UNCHANGED timestamp

DeliverOnNode ==
  \E n \in nodeIds :
    /\ Len(deliverQueues[n]) > 0
    /\ \E <<command, payload>> \in {Head(deliverQueues[n])} :
        Deliver(n, command, payload)
    /\ deliverQueues' = [deliverQueues EXCEPT ![n] = Tail(deliverQueues[n])]
  /\ UNCHANGED timestamp

DeliverQueuesIsEmpty ==
  \A n \in nodeIds: Len(deliverQueues[n]) = 0

Terminating ==
  /\ DeliverQueuesIsEmpty
  /\ UNCHANGED vars

Init ==
  /\ values = [i \in nodeIds |-> {}]
  /\ deliverQueues = [i \in nodeIds |-> <<>>]
  /\ timestamp = 1

Next ==
  \/ RequestSetOnNode
  \/ RequestDeleteOnNode
  \/ DeliverOnNode
  \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(DeliverOnNode)

AllValuesEqual ==
  \A n1, n2 \in nodeIds:
    values[n1] = values[n2]
EventuallyConsistent == <>[]AllValuesEqual
====
