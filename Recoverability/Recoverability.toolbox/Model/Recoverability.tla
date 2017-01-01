--------------------------- MODULE Recoverability ---------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Msgs,          \* Set of all possible messages *\
          MaxAttempts,   \* Max number of processing inMemAttempts *\
          CacheSize, 
          NoneTx, InProgress, Committed,
          Effects, Errors
          

ASSUME /\ MaxAttempts \in Nat


(*

--fair algorithm ReceiveWithRetries {
    variables tx             = [m \in Msgs |-> [state |-> NoneTx, ops |-> {}]],
              cachedAttempts = [m \in Msgs |-> 0],
              totalAttempts  = cachedAttempts;
              
              crashes = FALSE;
              
    macro StartTx(msg)    { tx[msg].state := InProgress; }
    macro CommitTx(msg)   { tx[msg].state := Committed; }
    macro RollbackTx(msg) { tx[msg].state := NoneTx || tx[msg].ops := {}; }
    
    macro Crash()
        { tx             := [m \in Msgs |-> [state |-> NoneTx, ops |-> {}]];
          cachedAttempts := [m \in Msgs |-> 0];
        }
    
    macro RecordAttempt(msg)
        { totalAttempts[msg]  := totalAttempts[msg] + 1;
          
          \* If cache size exceeded than remove one item         
          if(Cardinality({m \in Msgs: m # msg /\ cachedAttempts[m] # 0}) < CacheSize)
            { cachedAttempts[msg] := cachedAttempts[msg] + 1; }
          else 
            { with(invMsg = CHOOSE x \in Msgs : cachedAttempts[x] > 0 /\ x # msg)
                { cachedAttempts[msg]:= cachedAttempts[msg] + 1 ||
                  cachedAttempts[invMsg] := 0; 
                }
            }
        }
    
    macro ProcessingOk(msg) { tx[msg].ops := tx[msg].ops \cup { Effects }; }
    
    macro ProcessingErr(msg) 
        {  if (cachedAttempts[msg] < MaxAttempts)
            { RecordAttempt(msg);
              RollbackTx(msg);
            }
           else { tx[msg].ops := tx[msg].ops \cup { Errors }; } 
        }
    
    {
      while (\E m \in Msgs : tx[m].state # Committed)               
          {    either  { with (msg \in {c \in Msgs : tx[c].state = NoneTx})    
                            { StartTx(msg); } 
                       }
               or      { with (msg \in {c \in Msgs : tx[c].state = InProgress /\ tx[c].ops = {} })
                            {  either { ProcessingOk(msg); }
                               or     { ProcessingErr(msg); }
                            }
                       } 
               or      { with (msg \in {c \in Msgs : tx[c].state = InProgress /\ tx[c].ops # {} })
                            { CommitTx(msg); } 
                       }
               or      { with (msg \in {c \in Msgs: tx[c].state # NoneTx})
                            { RollbackTx(msg); }
                       }
               or      { await crashes = TRUE;
                         Crash();
                       }
          }
    } 
} 

*)
\* BEGIN TRANSLATION
VARIABLES tx, cachedAttempts, totalAttempts, crashes, pc

vars == << tx, cachedAttempts, totalAttempts, crashes, pc >>

Init == (* Global variables *)
        /\ tx = [m \in Msgs |-> [state |-> NoneTx, ops |-> {}]]
        /\ cachedAttempts = [m \in Msgs |-> 0]
        /\ totalAttempts = cachedAttempts
        /\ crashes = FALSE
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF \E m \in Msgs : tx[m].state # Committed
               THEN /\ \/ /\ \E msg \in {c \in Msgs : tx[c].state = NoneTx}:
                               tx' = [tx EXCEPT ![msg].state = InProgress]
                          /\ UNCHANGED <<cachedAttempts, totalAttempts>>
                       \/ /\ \E msg \in {c \in Msgs : tx[c].state = InProgress /\ tx[c].ops = {} }:
                               \/ /\ tx' = [tx EXCEPT ![msg].ops = tx[msg].ops \cup { Effects }]
                                  /\ UNCHANGED <<cachedAttempts, totalAttempts>>
                               \/ /\ IF cachedAttempts[msg] < MaxAttempts
                                        THEN /\ totalAttempts' = [totalAttempts EXCEPT ![msg] = totalAttempts[msg] + 1]
                                             /\ IF Cardinality({m \in Msgs: m # msg /\ cachedAttempts[m] # 0}) < CacheSize
                                                   THEN /\ cachedAttempts' = [cachedAttempts EXCEPT ![msg] = cachedAttempts[msg] + 1]
                                                   ELSE /\ LET invMsg == CHOOSE x \in Msgs : cachedAttempts[x] > 0 /\ x # msg IN
                                                             cachedAttempts' = [cachedAttempts EXCEPT ![msg] = cachedAttempts[msg] + 1,
                                                                                                      ![invMsg] = 0]
                                             /\ tx' = [tx EXCEPT ![msg].state = NoneTx,
                                                                 ![msg].ops = {}]
                                        ELSE /\ tx' = [tx EXCEPT ![msg].ops = tx[msg].ops \cup { Errors }]
                                             /\ UNCHANGED << cachedAttempts, 
                                                             totalAttempts >>
                       \/ /\ \E msg \in {c \in Msgs : tx[c].state = InProgress /\ tx[c].ops # {} }:
                               tx' = [tx EXCEPT ![msg].state = Committed]
                          /\ UNCHANGED <<cachedAttempts, totalAttempts>>
                       \/ /\ \E msg \in {c \in Msgs: tx[c].state # NoneTx}:
                               tx' = [tx EXCEPT ![msg].state = NoneTx,
                                                ![msg].ops = {}]
                          /\ UNCHANGED <<cachedAttempts, totalAttempts>>
                       \/ /\ crashes = TRUE
                          /\ tx' = [m \in Msgs |-> [state |-> NoneTx, ops |-> {}]]
                          /\ cachedAttempts' = [m \in Msgs |-> 0]
                          /\ UNCHANGED totalAttempts
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << tx, cachedAttempts, totalAttempts >>
         /\ UNCHANGED crashes

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION


EitherFailedOrProcessed == \A m \in Msgs : tx[m].state = Committed => \/ tx[m].ops = { Effects }
                                                                      \/ tx[m].ops = { Errors }
                                                                                                                                            
                                             
NoMoreThanMaxAttempts == \A m \in Msgs: totalAttempts[m] <= MaxAttempts

=============================================================================
\* Modification History
\* Last modified Sun Jan 01 22:34:20 CET 2017 by Tomasz Masternak
\* Created Tue Dec 27 20:32:15 CET 2016 by Tomasz Masternak
