--------------------------- MODULE Recoverability ---------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Msgs,          \* Set of all possible messages *\
          MaxAttempts,   \* Max number of processing inMemAttempts *\
          CacheSize, 
          Crashes,
          Processes
          
ASSUME /\ MaxAttempts \in Nat
       /\ CacheSize \in Nat /\ CacheSize > 2 
       /\ Crashes \in {TRUE, FALSE}
       /\ Processes \subseteq Nat

NoProc == 0

NoneTx   == "noneTx"
Committed == "commitedTx"
Effects   == "effects"
Errors   == "errors"


VARIABLES tx, cachedAttempts, totalAttempts

vars == << tx, cachedAttempts, totalAttempts >>

Init == (* Global variables *)
        /\ tx = [m \in Msgs |-> [proc |-> NoProc, state |-> NoneTx, ops |-> {}]]
        /\ cachedAttempts = [p \in Processes |-> [m \in Msgs |-> 0]]
        /\ totalAttempts = [m \in Msgs |-> 0]


ProcessingOk ==
    \E p \in Processes :
    \E m \in Msgs :
        /\ tx[m].state = NoneTx
        /\ cachedAttempts[p][m] < MaxAttempts
        /\ tx' = [tx EXCEPT ![m] = [proc |-> p, state |-> Committed, ops |-> {Effects}]]
        /\ totalAttempts' = [totalAttempts EXCEPT ![m] = @ + 1]
        /\ UNCHANGED << cachedAttempts >>
        
ProcessingErr ==
    \E p \in Processes :
    \E m \in Msgs :
        /\ tx[m].state = NoneTx
        /\ cachedAttempts[p][m] < MaxAttempts
        /\ totalAttempts' = [totalAttempts EXCEPT ![m] = @ + 1]
        /\ IF Cardinality({x \in Msgs: x # m /\ cachedAttempts[p][x] # 0}) < CacheSize
           THEN /\ cachedAttempts' = [cachedAttempts EXCEPT ![p] = [@ EXCEPT ![m] = @ + 1]]
           ELSE /\ LET invM == CHOOSE x \in Msgs : cachedAttempts[p][x] > 0 /\ x # m IN
                   cachedAttempts' = [cachedAttempts EXCEPT ![p] = [@ EXCEPT ![m] = @ + 1, ![invM] = 0]]
        /\ UNCHANGED << tx >>           

\* Message moved to error queue because number or attempts exceeded max
MoveToError == 
    \E p \in Processes :
    \E m \in Msgs : 
        /\ tx[m].state = NoneTx 
        /\ cachedAttempts[p][m] >= MaxAttempts 
        /\ tx' = [tx EXCEPT ![m] = [proc |-> p, state |-> Committed, ops |-> {Errors}]]
        /\ UNCHANGED << cachedAttempts, totalAttempts >>

\* On crash attempts cache is cleared
ProcessCrash == 
    /\ Crashes = TRUE
    /\ \E p \in Processes :
        /\ cachedAttempts' = [cachedAttempts EXCEPT ![p] = [m \in Msgs |-> 0]]
        /\ UNCHANGED totalAttempts

Next == 
    \/ ProcessCrash 
    \/ MoveToError
    \/ ProcessingOk
    \/ ProcessingErr
    \/ /\ \A m \in Msgs : tx[m].state = Committed \* Prevent deadlock detection
       /\ UNCHANGED vars 


Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)


\* END TRANSLATION


\*TransactionsAreAppendOnly == \A m \in Msgs: \/ Cardinality(tx'[m].ops) >= Cardinality(tx[m].ops)
\*                                            \/ tx'[m].state = NoneTx


EitherFailedOrProcessed == \A m \in Msgs : tx[m].state = Committed => \/ tx[m].ops = { Effects }
                                                                      \/ tx[m].ops = { Errors }
                                                                                                                                            
                                             
NoMoreThanMaxAttempts == \A m \in Msgs: totalAttempts[m] <= MaxAttempts

=============================================================================
\* Modification History
\* Last modified Tue Jan 03 13:18:23 CET 2017 by Tomasz Masternak
\* Created Tue Dec 27 20:32:15 CET 2016 by Tomasz Masternak
