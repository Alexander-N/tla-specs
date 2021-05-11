---- MODULE step1 ----
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

vars == <<taskStates, lockState, waiters>>

Init ==
  /\ taskStates = [task \in Tasks |-> running]
  /\ lockState = unlocked
  /\ waiters = <<>>

Acquire(task) ==
  \* If a waiting task was woken up, it will be next. Guard this action so that no
  \* other task can acquire the lock in this case.
  /\ \A t \in Tasks: taskStates[t] /= wakeup
  /\ taskStates[task] = running
  /\ IF waiters = <<>> /\ lockState = unlocked THEN
      /\ taskStates' = [taskStates EXCEPT ![task] = acquired]
      /\ lockState' = locked
      /\ UNCHANGED waiters
     ELSE
      /\ taskStates' = [taskStates EXCEPT ![task] = waiting]
      /\ waiters' = Append(waiters, task)
      /\ UNCHANGED lockState

Release(task) ==
  /\ taskStates[task] = acquired
  /\ Assert(lockState = locked,
            "Lock is not acquired.")
  /\ lockState' = unlocked
  \* Wake up the first waiter who isn't cancelled.
  /\ LET TaskIsNotCancelled(t) == taskStates[t] /= canceled IN
     LET uncanceledWaiters == SelectSeq(waiters, TaskIsNotCancelled) IN
    \* Every task is done after it has acquired and released the lock once.
     IF uncanceledWaiters = <<>> THEN
       taskStates' = [taskStates EXCEPT ![task] = done]
     ELSE
       LET nextTask == Head(uncanceledWaiters) IN
         /\ taskStates' = [taskStates EXCEPT
              ![task] = done,
              ![nextTask] = wakeup
            ]
  /\ UNCHANGED waiters

\* Allow one of the waiting tasks to acquire the lock and remove it from the list
\* of waiters. Represents
\* https://github.com/python/asyncio/blob/27218fa/asyncio/locks.py#L175-L180
WakeUp(task) ==
  /\ taskStates[task] = wakeup
  /\ Assert(lockState = unlocked,
            "Lock is not unlocked.")
  /\ taskStates' = [taskStates EXCEPT ![task] = acquired]
  /\ lockState' = locked
  /\ waiters' = SelectSeq(waiters, LAMBDA t: t /= task)

\* This action Represents the possibility that every task can be canceled after
\* each step.
Cancel(task) ==
  /\ taskStates' = [taskStates EXCEPT ![task] = canceled]
  /\ UNCHANGED <<waiters, lockState>>

AllDone == \A task \in Tasks: taskStates[task] = done \/ taskStates[task] = canceled
\* Allow infinite stuttering to prevent deadlock on termination.
Finished == /\ AllDone
            /\ UNCHANGED vars
Next == \E task \in Tasks:
  \/ Acquire(task)
  \/ Release(task)
  \/ WakeUp(task)
  \/ Cancel(task)
  \/ Finished

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A t \in Tasks:
    /\ WF_vars(Release(t))
    /\ WF_vars(Acquire(t))
    /\ WF_vars(WakeUp(t))

TypeInvariant ==
  /\ \A t \in Tasks:
      taskStates[t] \in {acquired, waiting, running, canceled, done, wakeup}
  /\ lockState \in {locked, unlocked}

\* There can not be two tasks holding the lock at the same time.
NotMoreThanOneAcquired ==
  \A t1 \in Tasks: \A t2 \in Tasks \ {t1}:
    taskStates[t1] = acquired => taskStates[t2] /= acquired

\* If the lock is locked at some point it has to get unlocked eventually.
LockGetsUnlocked ==
  lockState = locked ~> lockState = unlocked

Termination == <>AllDone
====
