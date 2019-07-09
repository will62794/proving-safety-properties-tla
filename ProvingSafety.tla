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

\* The proof structure.
THEOREM Spec => []Mutex
  \*
  \* Original proof step written manually.
  \* 
 <1>1_Original. Init => Inv
    <2>0. SUFFICES ASSUME Init
                   PROVE Inv
          OBVIOUS
    <2>1. Init => TypeOK
    <2>2. Init => \A i \in {0,1} : 
            /\ (flag[i] = TRUE) <=> (pc[i] \in {"s2", "cs", "s3"})
            /\ pc[i] = "cs" => (flag[1-i] = FALSE) \/ (pc[1-i] = "s2")
    <2>3. QED
        BY <2>1, <2>2 DEF Inv
 \*
 \* <1>1a. is an alternate way to decompose step <1>1.
 \*
 <1>1a. ASSUME Init
        PROVE Inv
     <2>1a. TypeOK
     <2>2a. \A i \in {0,1} : 
                /\ (flag[i] = TRUE) <=> (pc[i] \in {"s2", "cs", "s3"})
                /\ pc[i] = "cs" => (flag[1-i] = FALSE) \/ (pc[1-i] = "s2")
     <2>3a. QED BY <2>1a, <2>2a DEF Inv
 \*
 \* Automatically decomposed proof step.              
 \*
 <1>1. Init => Inv
   <2> SUFFICES ASSUME Init
                PROVE  Inv
     OBVIOUS
   <2>1. TypeOK 
        BY DEF Init, Inv, TypeOK, ProcSet
   <2>2. \A i \in {0, 1} :
              /\ (flag[i] = TRUE) <=> (pc[i] \in {"s2", "cs", "s3"})
              /\ pc[i] = "cs" => 
                  \/ flag[1-i] = FALSE 
                  \/ pc[1-i] = "s2"
     <3> SUFFICES ASSUME NEW i \in {0, 1}
                  PROVE  /\ (flag[i] = TRUE) <=> (pc[i] \in {"s2", "cs", "s3"})
                         /\ pc[i] = "cs" => 
                             \/ flag[1-i] = FALSE 
                             \/ pc[1-i] = "s2"
       OBVIOUS
     <3>1. (flag[i] = TRUE) <=> (pc[i] \in {"s2", "cs", "s3"}) BY DEF Init, Inv, TypeOK, ProcSet
\*        <4>1a. pc[i] = "s1" /\ flag[i] = FALSE
\*        <4>2a. QED BY <4>1a DEF Init 
     <3>2. pc[i] = "cs" => 
            \/ flag[1-i] = FALSE 
            \/ pc[1-i] = "s2"
       BY DEF Init, Inv, TypeOK
     <3>3. QED
       BY <3>1, <3>2
        
   <2>3. QED
     BY <2>1, <2>2 DEF Inv
 <1>2. Inv /\ [Next]_vars => Inv'
 <1>3. Inv => Mutex
 <1>4. QED
    BY <1>1, <1>2, <1>3, PTL DEF Spec


===================================================================
\* Modification History
\* Last modified Tue Jul 09 16:35:51 EDT 2019 by williamschultz
\* Created Mon Jun 10 11:44:50 EDT 2019 by williamschultz
