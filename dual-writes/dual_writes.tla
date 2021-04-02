---- MODULE dual_writes ----
EXTENDS TLC, Integers
CONSTANTS Clients, Database, Cache

Storages == {Database, Cache}

(*--algorithm dual_writes
variables
  StorageValues = [s \in Storages |-> 0];
fair process client \in Clients
begin
  WriteDatabase:
    StorageValues[Database] := self;
  WriteCache:
    StorageValues[Cache] := self;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "4f9acc13" /\ chksum(tla) = "4ffa7d85")
VARIABLES StorageValues, pc

vars == << StorageValues, pc >>

ProcSet == (Clients)

Init == (* Global variables *)
        /\ StorageValues = [s \in Storages |-> 0]
        /\ pc = [self \in ProcSet |-> "WriteDatabase"]

WriteDatabase(self) == /\ pc[self] = "WriteDatabase"
                       /\ StorageValues' = [StorageValues EXCEPT ![Database] = self]
                       /\ pc' = [pc EXCEPT ![self] = "WriteCache"]

WriteCache(self) == /\ pc[self] = "WriteCache"
                    /\ StorageValues' = [StorageValues EXCEPT ![Cache] = self]
                    /\ pc' = [pc EXCEPT ![self] = "Done"]

client(self) == WriteDatabase(self) \/ WriteCache(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Clients: client(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : WF_vars(client(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

AllValuesEqual ==
  \A s1, s2 \in Storages:
    StorageValues[s1] = StorageValues[s2]
EventuallyConsistent == <>[]AllValuesEqual

====
