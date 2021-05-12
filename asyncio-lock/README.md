# asyncio-lock

The idea is to take some real bugs which have been present at some point in
Python's [asyncio
lock](https://docs.python.org/3/library/asyncio-sync.html#lock) and model the
problems and the fixes iteratively.

## Step 1
[step1.tla](step1.tla) models [this old
version](https://github.com/python/asyncio/blob/27218fa/asyncio/locks.py#L89-L201)
of Python's asyncio lock. The expectation was to get one of the issues mentioned
in https://bugs.python.org/issue27585 but instead we get the following error
trace:
```tla
1: Init
/\ waiters = <<>>
/\ lockState = unlocked
/\ taskStates = (Task1 :> running @@ Task2 :> running @@ Task3 :> running)

2: Cancel
/\ waiters = <<>>
/\ lockState = unlocked
/\ taskStates = (Task1 :> running @@ Task2 :> canceled @@ Task3 :> running)

3: Acquire
/\ waiters = <<>>
/\ lockState = locked
/\ taskStates = (Task1 :> acquired @@ Task2 :> canceled @@ Task3 :> running)

4: Cancel
/\ waiters = <<>>
/\ lockState = locked
/\ taskStates = (Task1 :> canceled @@ Task2 :> canceled @@ Task3 :> running)

5: Acquire
/\ waiters = <<Task3>>
/\ lockState = locked
/\ taskStates = (Task1 :> canceled @@ Task2 :> canceled @@ Task3 :> waiting)

6: Stuttering
```

What this shows is that we can get a deadlock by cancelling the task which holds
the lock. This is something to be aware of, but from the asyncio library's
perspective, there is [nothing which can be
done](https://bugs.python.org/issue43991). Libraries using [structured
concurrency](https://vorpus.org/blog/notes-on-structured-concurrency-or-go-statement-considered-harmful/)
approaches like [trio](https://github.com/python-trio/trio) seem like a natural
fit to handle cases like this (https://github.com/python-trio/trio/issues/182).

## Step 2
The bug we where originally interested in happens when a waiting task is
canceled. To get to this issue, in [step2.tla](step2.tla) we restrict the
`Cancel` action to only cancel tasks which are in the `waiting` state:
```diff
 Cancel(task) ==
+  \* Only cancel waiting tasks.
+  /\ taskStates[task] = waiting
   /\ taskStates' = [taskStates EXCEPT ![task] = canceled]
   /\ UNCHANGED <<waiters, lockState>>
```
This works, the error trace shows the problem:
```tla
1: Init
/\ waiters = <<>>
/\ lockState = unlocked
/\ taskStates = (Task1 :> running @@ Task2 :> running @@ Task3 :> running)

2: Acquire
/\ waiters = <<>>
/\ lockState = locked
/\ taskStates = (Task1 :> running @@ Task2 :> acquired @@ Task3 :> running)

3: Acquire
/\ waiters = <<Task1>>
/\ lockState = locked
/\ taskStates = (Task1 :> waiting @@ Task2 :> acquired @@ Task3 :> running)

4: Cancel
/\ waiters = <<Task1>>
/\ lockState = locked
/\ taskStates = (Task1 :> canceled @@ Task2 :> acquired @@ Task3 :> running)

5: Release
/\ waiters = <<Task1>>
/\ lockState = unlocked
/\ taskStates = (Task1 :> canceled @@ Task2 :> done @@ Task3 :> running)

6: Acquire
/\ waiters = <<Task1, Task3>>
/\ lockState = unlocked
/\ taskStates = (Task1 :> canceled @@ Task2 :> done @@ Task3 :> waiting)

7: Stuttering
```

## Step 3
The bug is that the lock can't be acquired when there are waiters in the queue,
even if they have been all canceled. The fix is to simply account for this case
https://github.com/python/asyncio/pull/393:
```diff
From bbe53f381fbade4f8c1d04b2a463270710f1392a Mon Sep 17 00:00:00 2001
From: Guido van Rossum <guido@python.org>
Date: Thu, 4 Aug 2016 09:12:07 -0700
Subject: [PATCH] Avoid deadlock when a cancelled future is in self._waiters.

---
 asyncio/locks.py | 2 +-
 1 file changed, 1 insertion(+), 1 deletion(-)

diff --git a/asyncio/locks.py b/asyncio/locks.py
index 741aaf27..deefc938 100644
--- a/asyncio/locks.py
+++ b/asyncio/locks.py
@@ -166,7 +166,7 @@ def acquire(self):
         This method blocks until the lock is unlocked, then sets it to
         locked and returns True.
         """
-        if not self._waiters and not self._locked:
+        if not self._locked and all(w.cancelled() for w in self._waiters):
             self._locked = True
             return True
```

We do the same in [step3.tla](step3.tla)
```diff
 Acquire(task) ==
   \* If a waiting task was woken up, it will be next. Guard this action so that no
   \* other task can acquire the lock in this case.
   /\ \A t \in Tasks: taskStates[t] /= wakeup
   /\ taskStates[task] = running
-  /\ IF waiters = <<>> /\ lockState = unlocked THEN
+  /\ IF lockState = unlocked /\ \A t \in Range(waiters): taskStates[t] = canceled THEN
       /\ taskStates' = [taskStates EXCEPT ![task] = acquired]
       /\ lockState' = locked
       /\ UNCHANGED waiters
```
This seems to fix the issue, we don't get an error anymore.
## Step 4
There is another bug mentioned in https://bugs.python.org/issue43991, which
happens when a bug is canceled immediately after it was woken up. In this case
the lock is not released after `release` was called and no other task is woken
up, which means all other waiting tasks will wait forever.

The issue is easy to reproduce with a small change in [step4.tla](step4.tla):
```diff
 Cancel(task) ==
-  \* Only cancel waiting tasks.
-  /\ taskStates[task] = waiting
+  \* Cancel waiting tasks and tasks just after they have been woken up.
+  /\ taskStates[task] \in {waiting, wakeup}
   /\ taskStates' = [taskStates EXCEPT ![task] = canceled]
   /\ UNCHANGED <<waiters, lockState>>
```

Trace:
```tla
1: Init
/\ waiters = <<>>
/\ taskStates = (Task1 :> running @@ Task2 :> running @@ Task3 :> running)
/\ lockState = unlocked

2: Acquire
/\ waiters = <<>>
/\ taskStates = (Task1 :> running @@ Task2 :> running @@ Task3 :> acquired)
/\ lockState = locked

3: Acquire
/\ waiters = <<Task2>>
/\ taskStates = (Task1 :> running @@ Task2 :> waiting @@ Task3 :> acquired)
/\ lockState = locked

4: Acquire
/\ waiters = <<Task2, Task1>>
/\ taskStates = (Task1 :> waiting @@ Task2 :> waiting @@ Task3 :> acquired)
/\ lockState = locked

5: Release
/\ waiters = <<Task2, Task1>>
/\ taskStates = (Task1 :> waiting @@ Task2 :> wakeup @@ Task3 :> done)
/\ lockState = unlocked

6: Cancel
/\ waiters = <<Task2, Task1>>
/\ taskStates = (Task1 :> waiting @@ Task2 :> canceled @@ Task3 :> done)
/\ lockState = unlocked

7: Stuttering
```

[The fix](https://github.com/python/asyncio/pull/467/files) is again very
simple, but to model it we would have to change our spec so that we know what
state the task was in when it was canceled. One way would be to use structures
for tasks like
```tla
[state |-> waiting, canceled |-> TRUE]
```
