--------------------------------------- MODULE ProvingSafety ---------------------------------------
EXTENDS Integers, TLAPS

(*****
 --algorithm SimpleMutex {
      variables flag = [i \in {0, 1} |-> FALSE];
      process (proc \in {0,1}) {
        s1: while (TRUE) {
              flag[self] := TRUE ;
        s2:   await flag[1-self] = FALSE ;
        cs:   skip ;
        s3:   flag[self] := FALSE
                                            }     }     }                                           
*****)
\* BEGIN TRANSLATION
VARIABLES flag, pc

vars == << flag, pc >>

ProcSet == ({0,1})

Init == (* Global variables *)
        /\ flag = [i \in {0, 1} |-> FALSE]
        /\ pc = [self \in ProcSet |-> "s1"]

s1(self) == /\ pc[self] = "s1"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "s2"]

s2(self) == /\ pc[self] = "s2"
            /\ flag[1-self] = FALSE
            /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ flag' = flag

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "s3"]
            /\ flag' = flag

s3(self) == /\ pc[self] = "s3"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "s1"]

proc(self) == s1(self) \/ s2(self) \/ cs(self) \/ s3(self)

Next == (\E self \in {0,1}: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

Mutex == ~(pc[0] = "cs" /\ pc[1] = "cs")

\*
\* Proof
\*

TypeOK == /\ flag \in [{0, 1} -> BOOLEAN]
          /\ pc \in [{0, 1} -> {"s1", "s2", "cs", "s3"}]

\* The inductive invariant.
Inv == 
    /\ TypeOK
    /\ \A i \in {0, 1} :
            \* flag[i] is true iff we are at label s2, cs, or s3, for all processes.
            /\ (flag[i] = TRUE) <=> (pc[i] \in {"s2", "cs", "s3"})
            \* If we are in the critical section, then the other flag must be FALSE.
            /\ pc[i] = "cs" => 
                \/ flag[1-i] = FALSE 
                \* If we don't include this extra part of the disjunct, then this overall statement is not an invariant,
                \* since it's possible that after we enter the critical section, the other process sets its flag
                \* to TRUE (at label s1), even if it still can't enter the critical section.
                \/ pc[1-i] = "s2"

THEOREM Spec => []Mutex
 <1>1. Init => Inv
 <1>2. Inv /\ [Next]_vars => Inv'
 <1>3. Inv => Mutex
 <1>4. QED
    BY <1>1, <1>2, <1>3, PTL DEF Spec


===================================================================
\* Modification History
\* Last modified Tue Jul 02 15:59:44 EDT 2019 by williamschultz
\* Created Mon Jun 10 11:44:50 EDT 2019 by williamschultz
