----------------------------- MODULE aiorwlock_bug ------------------------------
EXTENDS Naturals, Sequences, Integers, FiniteSets
CONSTANTS Task
ASSUME /\ Task # {}

VARIABLES State,
          Lock

vars == <<State, Lock>>

-----------------------------------------------------------------------------
TypeOK == /\ Lock \in [Task -> {"Read", "Write", "WriteRead", "Waiting", "Finished"}]
          /\ State >= -2
LockInit == Lock = [t \in Task |-> "Waiting"] /\ State = 0
-----------------------------------------------------------------------------


Rlocked == State > 0
Wlocked == State < 0
Unlocked == State = 0

WOwn(t) == Lock[t] \in {"Write"}

RAquire(t) == \/ /\ ~Wlocked
                 /\ Lock[t] \in {"Waiting"}
                 /\ Lock' = [Lock EXCEPT ![t] = "Read"]
                 /\ State' = State + 1
              \/ /\ WOwn(t)
                 /\ Lock' = [Lock EXCEPT ![t] = "WriteRead"]
                 /\ State' = State + 1

WAquire(t) == /\ Unlocked
              /\ Lock[t] \in {"Waiting"}
              /\ Lock' = [Lock EXCEPT ![t] = "Write"]
              /\ State' = State - 1

RRelease(t) == \/ /\ Rlocked /\ Lock[t] = "Read"
                  /\ State' = State - 1 /\ Lock' = [Lock EXCEPT ![t] = "Finished"]
               \/ /\ Rlocked /\ Lock[t] = "WriteRead"
                  /\ State' = State - 1 /\ Lock' = [Lock EXCEPT ![t] = "Write"]

WRelease(t) == \/ /\ Wlocked /\ Lock[t] = "Write"
                  /\ State' = State + 1 /\ Lock' = [Lock EXCEPT ![t] = "Finished"]
               \/ /\ Wlocked /\ Lock[t] = "WriteRead"
                  /\ State' = State + 1 /\ Lock' = [Lock EXCEPT ![t] = "Read"]


(* Allow infinite stuttering to prevent deadlock. *)
Finished == /\ \A t \in Task: Lock[t] = "Finished"
            /\ UNCHANGED vars
-----------------------------------------------------------------------------

Next == \E t \in Task: RAquire(t) \/ WAquire(t) \/ RRelease(t) \/ WRelease(t) \/ Finished

Spec == LockInit /\ [][Next]_vars


LockInv ==
    \A t1 \in Task : \A t2 \in (Task \ {t1}):
      Lock[t1] \in {"Write", "WriteRead"} => Lock[t2] \in {"Waiting", "Finished"}
-----------------------------------------------------------------------------

THEOREM Spec => [](TypeOK /\ LockInv)

=============================================================================
