---- MODULE step3 ----
EXTENDS TLC, Sequences

CONSTANTS
  Tasks,
  \* Task states
  running,
  acquired,
  waiting,
  wakeup,
  canceled,
  done,
  \* Lock states
  locked,
  unlocked

VARIABLES taskStates, lockState, waiters

s1 == INSTANCE step1
s2 == INSTANCE step2

vars == <<taskStates, lockState, waiters>>

Range(f) == {f[x]: x \in DOMAIN f}

\* Fix as in https://github.com/python/asyncio/pull/393
Acquire(task) ==
  \* If a waiting task was woken up, it will be next. Guard this action so that no
  \* other task can acquire the lock in this case.
  /\ \A t \in Tasks: taskStates[t] /= wakeup
  /\ taskStates[task] = running
  /\ IF lockState = unlocked /\ \A t \in Range(waiters): taskStates[t] = canceled THEN
      /\ taskStates' = [taskStates EXCEPT ![task] = acquired]
      /\ lockState' = locked
      /\ UNCHANGED waiters
     ELSE
      /\ taskStates' = [taskStates EXCEPT ![task] = waiting]
      /\ waiters' = Append(waiters, task)
      /\ UNCHANGED lockState


Next == \E task \in Tasks:
  \/ Acquire(task)
  \/ s2!Cancel(task)
  \/ s1!Release(task)
  \/ s1!WakeUp(task)
  \/ s1!Finished

Spec ==
  /\ s1!Init
  /\ [][Next]_vars
  /\ \A t \in Tasks:
    /\ WF_vars(Acquire(t))
    /\ WF_vars(s1!Release(t))
    /\ WF_vars(s1!WakeUp(t))

TypeInvariant == s1!TypeInvariant
NotMoreThanOneAcquired == s1!NotMoreThanOneAcquired
LockGetsUnlocked == s1!LockGetsUnlocked
Termination == s1!Termination
====
