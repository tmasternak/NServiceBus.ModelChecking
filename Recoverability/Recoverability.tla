--------------------------- MODULE Recoverability ---------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS Msgs,          \* Set of all possible messages *\
          MaxAttempts,   \* Max number of processing inMemAttempts *\
          CacheSize, 
          Crashes,
          TxTimeouts,
          Processes
          
ASSUME /\ MaxAttempts \in Nat
       /\ CacheSize \in Nat /\ CacheSize > 1 
       /\ Crashes \in {TRUE, FALSE}
       /\ Processes \subseteq Nat

NoProc == 0
Procs == Processes \cup {NoProc}

\* Transaction states
InProgress == "inprogress"
Committed  == "commited"
TxStates   == {InProgress, Committed}

    
\* Continuations
ProcessCont      == "process"
SendToErrorsCont == "sendToErrors"
RollbackCont     == "rollback"
CommitCont       == "commit"
NoCont           == "noCon" 
Conts            == {ProcessCont, RollbackCont, CommitCont, SendToErrorsCont, NoCont}

VARIABLES tx, cachedAttempts, totalAttempts

vars == << tx, cachedAttempts, totalAttempts >>

TypeOK ==
    /\ tx \in [Msgs -> SUBSET [proc: Procs, state: TxStates, cont: Conts]]
    /\ cachedAttempts \in [Processes -> [Msgs -> Nat]]                         
    /\ totalAttempts \in [Msgs -> Nat]
    
Init == (* Global variables *)
    /\ tx = [m \in Msgs |-> {}]
    /\ cachedAttempts = [p \in Processes |-> [m \in Msgs |-> 0]]
    /\ totalAttempts = [m \in Msgs |-> 0]


\* On crash attempts cache is cleared
ProcessCrash == 
    /\ Crashes = TRUE
    /\ \E p \in Processes :
        /\ cachedAttempts' = [cachedAttempts EXCEPT ![p] = [m \in Msgs |-> 0]]
        /\ \A m \in Msgs :
            /\ tx' = [tx EXCEPT ![m] = {x \in @ : x.proc # p}]
        /\ UNCHANGED <<totalAttempts >>

BeginTx ==
   \E m \in Msgs :
   \E p \in Processes :
       /\ \/ /\ TxTimeouts = FALSE 
             /\ Cardinality(tx[m]) = 0 \* no overlapping transactions 
          \/ /\ TxTimeouts = TRUE
             /\ Cardinality(tx[m]) < 2
       /\ \/ /\ cachedAttempts[p][m] < MaxAttempts  \* Process the message
             /\ tx' = [tx EXCEPT ![m] = @ \cup {[proc |-> p, state |-> InProgress, cont |-> ProcessCont]}]
             /\ UNCHANGED << cachedAttempts, totalAttempts >>
          \/ /\ cachedAttempts[p][m] >= MaxAttempts \* Move the message to errors
             /\ tx' = [tx EXCEPT ![m] = @ \cup {[proc |-> p, state |-> InProgress, cont |-> SendToErrorsCont]}]
             /\ UNCHANGED << cachedAttempts, totalAttempts >> 
   
UpdateCache(m, p) ==
    /\ IF Cardinality({x \in Msgs: x # m /\ cachedAttempts[p][x] # 0}) < CacheSize
       THEN /\ cachedAttempts' = [cachedAttempts EXCEPT ![p] = [@ EXCEPT ![m] = IF @ + 1 > MaxAttempts THEN MaxAttempts ELSE @ + 1]]
       ELSE /\ LET invM == CHOOSE x \in Msgs : cachedAttempts[p][x] > 0 /\ x # m IN
               cachedAttempts' = [cachedAttempts EXCEPT ![p] = [@ EXCEPT ![m] = IF @ + 1 > MaxAttempts THEN MaxAttempts ELSE @ + 1, ![invM] = 0]]
               
ClearCache(m, p) ==
    /\ cachedAttempts' = [cachedAttempts EXCEPT ![p] = [@ EXCEPT ![m] = 0]]
    
SendToErrors ==
    \E m \in Msgs :
    \E t \in tx[m]:
        /\ t.cont = SendToErrorsCont
        /\ tx' = [tx EXCEPT ![m] = (@ \ {t}) \cup {[t EXCEPT !["cont"] = CommitCont]}]
        /\ ClearCache(m, t.proc)
        /\ UNCHANGED << totalAttempts >>
        
Process ==
    \E m \in Msgs :
    \E t \in tx[m] :
        /\ t.cont = ProcessCont
        /\ totalAttempts' = [totalAttempts EXCEPT ![m] = IF @ + 1 > 2*MaxAttempts THEN 2*MaxAttempts ELSE @ + 1]
        /\ \/ /\ tx' = [tx EXCEPT ![m] = (@ \ {t}) \cup {[t EXCEPT !["cont"] = CommitCont]}]    
              /\ ClearCache(m, t.proc)
           \/ /\ tx' = [tx EXCEPT ![m] = (@ \ {t}) \cup {[t EXCEPT !["cont"] = RollbackCont]}]
              /\ UpdateCache(m, t.proc)
               
CommitTx ==
    \E m \in Msgs :
    \E t \in tx[m] :
        \/ /\ t.cont = CommitCont
           /\ \A ot \in tx[m] :
                \/ ot = t       
                \/ ot.state # Committed
           /\ tx' = [tx EXCEPT ![m] = (@ \ {t}) \cup {[t EXCEPT !["state"] = Committed]}]
           /\ UNCHANGED << totalAttempts, cachedAttempts >>
        \/ /\ t.cont = RollbackCont
           /\ tx' = [tx EXCEPT ![m] = @ \ {t}]
           /\ UNCHANGED << totalAttempts, cachedAttempts >>
        \/ /\ t.cont \in {RollbackCont, CommitCont} \* This assumes that Rollback on tx can throw
           /\ tx' = [tx EXCEPT ![m] = @ \ {t}]
           /\ UpdateCache(m, t.proc)
           /\ UNCHANGED << totalAttempts>>
           

Next == 
 /\ \/ BeginTx
    \/ Process
    \/ SendToErrors
    \/ CommitTx
    \/ /\ \A m \in Msgs :
            \A t \in tx[m] : t.state = Committed \* Prevent deadlock detection
       /\ UNCHANGED vars 

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)


\* END TRANSLATION

                                                                                                                                                                                       
NoMoreThanMaxAttempts == \A m \in Msgs: totalAttempts[m] <= MaxAttempts

=============================================================================
\* Modification History
\* Last modified Wed Jan 04 23:32:02 CET 2017 by Tomasz Masternak
\* Created Tue Dec 27 20:32:15 CET 2016 by Tomasz Masternak
