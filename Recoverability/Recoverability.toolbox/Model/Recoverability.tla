--------------------------- MODULE Recoverability ---------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Msgs,          \* Set of all possible messages *\
          MaxAttempts,   \* Max number of processing inMemAttempts *\
          CacheSize, 
          Crashes
          
ASSUME /\ MaxAttempts \in Nat
       /\ CacheSize > 2
       /\ Crashes \in {TRUE, FALSE}

NoneTx   == "noneTx"
Committed == "commitedTx"
Effects   == "effects"
Errors   == "errors"


VARIABLES tx, cachedAttempts, totalAttempts

vars == << tx, cachedAttempts, totalAttempts >>

Init == (* Global variables *)
        /\ tx = [m \in Msgs |-> [state |-> NoneTx, ops |-> {}]]
        /\ cachedAttempts = [m \in Msgs |-> 0]
        /\ totalAttempts = cachedAttempts


ProcessingOk ==
    \E m \in Msgs :
        /\ tx[m].state = NoneTx
        /\ cachedAttempts[m] < MaxAttempts
        /\ tx' = [tx EXCEPT ![m] = [state |-> Committed, ops |-> {Effects}]]
        /\ totalAttempts' = [totalAttempts EXCEPT ![m] = @ + 1]
        /\ UNCHANGED << cachedAttempts >>
        
ProcessingErr ==
    \E m \in Msgs :
        /\ tx[m].state = NoneTx
        /\ cachedAttempts[m] < MaxAttempts
        /\ totalAttempts' = [totalAttempts EXCEPT ![m] = @ + 1]
        /\ IF Cardinality({x \in Msgs: x # m /\ cachedAttempts[x] # 0}) < CacheSize
           THEN /\ cachedAttempts' = [cachedAttempts EXCEPT ![m] = @ + 1]
           ELSE /\ LET invM == CHOOSE x \in Msgs : cachedAttempts[x] > 0 /\ x # m IN
                   cachedAttempts' = [cachedAttempts EXCEPT ![m] = @ + 1, ![invM] = 0]
        /\ UNCHANGED << tx >>           

\* Message moved to error queue because number or attempts exceeded max
MoveToError == 
    \E m \in Msgs : 
        /\ tx[m].state = NoneTx 
        /\ cachedAttempts[m] >= MaxAttempts 
        /\ tx' = [tx EXCEPT ![m] = [state |-> Committed, ops |-> {Errors}]]
        /\ UNCHANGED << cachedAttempts, totalAttempts >>

\* On crash all transactions are rollbacked and attempts cache is cleared
ProcessCrash == 
    /\ Crashes = TRUE
    /\ tx' = [m \in Msgs |-> IF tx[m].state # Committed THEN [state |-> NoneTx, ops |-> {}] ELSE tx[m]]
    /\ cachedAttempts' = [m \in Msgs |-> 0]
    /\ UNCHANGED totalAttempts

Next == 
    \/ ProcessCrash 
    \/ MoveToError
    \/ ProcessingOk
    \/ ProcessingErr


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
\* Last modified Mon Jan 02 15:00:27 CET 2017 by Tomasz Masternak
\* Created Tue Dec 27 20:32:15 CET 2016 by Tomasz Masternak
