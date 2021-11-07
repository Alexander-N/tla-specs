---- MODULE rate_limiter ----
EXTENDS TLC, Integers
CONSTANTS
  MAX_CLOCK,
  MAX_REQUESTS_PER_SECOND,
  MAX_ABORTS,
  Null
VARIABLES counter, expirationTime, clock, pc, abortCounter

vars == <<counter, expirationTime, clock, pc, abortCounter>>

Incr ==
  counter' = counter + 1

Expire(timeout) ==
  expirationTime' = clock + timeout

Init ==
  /\ counter = 0
  /\ expirationTime = Null
  /\ clock = 0
  /\ pc = "Incr"
  /\ abortCounter = 0

ClearExpiredValues ==
  IF clock + 1 = expirationTime
  THEN
    /\ counter' = 0
    /\ expirationTime' = Null
  ELSE
    UNCHANGED <<counter, expirationTime>>

TimeStep ==
  /\ clock < MAX_CLOCK
  /\ ClearExpiredValues
  /\ clock' = clock + 1
  /\ UNCHANGED <<pc, abortCounter>>

\* The process can be aborted. This state represents for example a crash, a
\* network problem or some other error.
Abort ==
  /\ abortCounter < MAX_ABORTS
  /\ abortCounter' = abortCounter + 1
  /\ pc' = "Abort"
  /\ UNCHANGED <<clock, counter, expirationTime>>

Recover ==
  /\ pc = "Abort"
  /\ pc' = "Incr"
  /\ UNCHANGED <<clock, counter, expirationTime, abortCounter>>

LimitApiCall ==
  \/
    /\ pc = "Incr"
    /\ clock < MAX_CLOCK
    /\ counter < MAX_REQUESTS_PER_SECOND
    /\ Incr
    /\ IF counter = 0
        THEN pc' = "Expire"
        ELSE pc' = "Incr"
    /\ UNCHANGED <<expirationTime, abortCounter, clock>>
  \/
    /\ pc = "Expire"
    /\ Expire(1)
    /\ pc' = "Incr"
    /\ UNCHANGED <<counter, abortCounter, clock>>

\* Incr and Expire in one atomic step, represents the variant with the Lua
\* script from the README.
LimitApiCallAtomic ==
  /\ pc = "Incr"
  /\ clock < MAX_CLOCK
  /\ counter < MAX_REQUESTS_PER_SECOND
  /\
    /\ Incr
    /\ IF counter = 0
        THEN Expire(1)
        ELSE UNCHANGED <<expirationTime>>
  /\ UNCHANGED <<clock, abortCounter, pc>>

Terminating ==
  /\ clock = MAX_CLOCK
  /\ ClearExpiredValues
  /\ UNCHANGED <<clock, pc, abortCounter>>

Next ==
  \/ LimitApiCall
  \/ Abort
  \/ Recover
  \/ TimeStep
  \/ Terminating

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

NextAtomic ==
  \/ LimitApiCallAtomic
  \/ Abort
  \/ Recover
  \/ TimeStep
  \/ Terminating

SpecAtomic ==
  /\ Init
  /\ [][NextAtomic]_vars
  /\ WF_vars(NextAtomic)

Range(f) == {f[x] : x \in DOMAIN f}
TypeInvariant ==
  /\ pc \in {"Incr", "Expire", "Abort"}
  /\ clock \in  0..MAX_CLOCK
  /\ counter \in Nat
  /\ expirationTime \in {Null} \union 1..MAX_CLOCK+1
  /\ abortCounter \in 0..MAX_ABORTS

\* Values are set to zero at their expiration time.
ExpirationTimeResetsCounter == expirationTime = clock => counter = 0

RequestsAreLimited == counter <= MAX_REQUESTS_PER_SECOND

OutOfRequests == counter = MAX_REQUESTS_PER_SECOND
NotAlwaysOutOfRequests == ~[](OutOfRequests \/ clock = 0)

\* At some point in the future the counter will be zero. Without the limitations of
\* model checking we could always have more requests coming in and we can only say
\* that the requests will always be zero at some point in the future. Since the
\* counter can always be increased by more requests coming in the real system would
\* satisfy []<>(counter = 0) but not <>[](counter = 0).
ValuesExpire == []<>(counter = 0)
====
