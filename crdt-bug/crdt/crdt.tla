---- MODULE crdt ----
EXTENDS TLC, FiniteSets, Naturals, Sequences
CONSTANTS MAX_TIMESTAMP, KEYS, VALUES, N_NODES
VARIABLES timestamp, values, deliverQueues

vars == <<timestamp, values, deliverQueues>>
nodeIds == 1..N_NODES

DeliverSet(n, t, k, v) ==
  LET previous == { <<tp, kp, vp>> \in values[n]: kp = k }  IN
  IF previous = {} \/ \A <<tp, kp, vp>> \in previous : tp < t THEN
    values' = [ values EXCEPT ![n] = (values[n] \ previous) \union {<<t, k, v>>} ]
  ELSE
    UNCHANGED values

DeliverDelete(n, t) ==
  values' = [values EXCEPT ![n] = {<<tp, k, v>> \in values[n] : tp /= t }]

Deliver(n, command, payload) ==
  \/ command = "set"
    /\ DeliverSet(n, payload[1], payload[2], payload[3])
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
  /\ timestamp' = timestamp + 1
  /\ Broadcast(n, "set", <<timestamp, k, v>>)

RequestDelete(n, k) ==
  \E <<t, kp, v>> \in values[n]:
    /\ kp = k
    /\ Broadcast(n, "delete", t)

RequestSetOnNode ==
  /\ timestamp < MAX_TIMESTAMP
  /\ \E <<n, k, v>> \in nodeIds \X KEYS \X VALUES : RequestSet(n, k, v)

RequestDeleteOnNode ==
  /\ \E <<n, k>> \in nodeIds \X KEYS : RequestDelete(n, k)
  /\ UNCHANGED timestamp

DeliverOnNode ==
  \E n \in nodeIds:
    /\ Len(deliverQueues[n]) > 0
    /\ \E <<command, payload>> \in {Head(deliverQueues[n])}:
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
