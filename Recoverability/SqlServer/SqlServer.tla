----------------------------- MODULE SqlServer -----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS NMsgs,
          NProcessors,
          NNodes,
          MaxFailedAttempts

ASSUME /\ NMsgs \in Nat
       /\ NProcessors \in Nat
       /\ NNodes \in Nat
       /\ MaxFailedAttempts \in Nat
          
(*
--algorithm ProcessWithRecoverability
{   variables msgs = 1..NMsgs,
              nodes = 1..NNodes,
              failedMsgs = {},
              attemptsPerMsg = [node \in 1..NNodes |-> [msg \in 1..NMsgs |-> 0]],
              processingsPerMsg = [msg \in 1..NMsgs |-> 0];

    define { Min(n,m) == IF n<m THEN n ELSE m }                           
    
    macro RecordFailure(nodeId, m) { attemptsPerMsg[nodeId][m] := Min(attemptsPerMsg[nodeId][m]+1, MaxFailedAttempts); }
    
    fair process(Processor \in 1..NProcessors)
    variable failedAttempts = 0, m = 0, nodeId = 0;
    {  p:  while(Cardinality(msgs) # 0)
           {         with (n \in nodes) {nodeId := n};
                     with (x \in msgs)  {m := x};
                     
                     failedAttempts := attemptsPerMsg[nodeId][m];
               
                hdl: if (failedAttempts >= MaxFailedAttempts)
                     { either { msgs := msgs \ {m};
                                failedMsgs := failedMsgs \cup {m}; 
                              }
                       or     { RecordFailure(nodeId, m); }
                     }
                     else
                     {    processingsPerMsg[m] := processingsPerMsg[m] + 1;
                   
                      ex: either { msgs := msgs \ {m}; }
                          or     { RecordFailure(nodeId, m); }                     
                     }
         } 
    }
}
*)
\* BEGIN TRANSLATION
VARIABLES msgs, nodes, failedMsgs, attemptsPerMsg, processingsPerMsg, pc

(* define statement *)
Min(n,m) == IF n<m THEN n ELSE m

VARIABLES failedAttempts, m, nodeId

vars == << msgs, nodes, failedMsgs, attemptsPerMsg, processingsPerMsg, pc, 
           failedAttempts, m, nodeId >>

ProcSet == (1..NProcessors)

Init == (* Global variables *)
        /\ msgs = 1..NMsgs
        /\ nodes = 1..NNodes
        /\ failedMsgs = {}
        /\ attemptsPerMsg = [node \in 1..NNodes |-> [msg \in 1..NMsgs |-> 0]]
        /\ processingsPerMsg = [msg \in 1..NMsgs |-> 0]
        (* Process Processor *)
        /\ failedAttempts = [self \in 1..NProcessors |-> 0]
        /\ m = [self \in 1..NProcessors |-> 0]
        /\ nodeId = [self \in 1..NProcessors |-> 0]
        /\ pc = [self \in ProcSet |-> "p"]

p(self) == /\ pc[self] = "p"
           /\ IF Cardinality(msgs) # 0
                 THEN /\ \E n \in nodes:
                           nodeId' = [nodeId EXCEPT ![self] = n]
                      /\ m' = [m EXCEPT ![self] = CHOOSE x \in msgs : TRUE]
                      /\ failedAttempts' = [failedAttempts EXCEPT ![self] = attemptsPerMsg[nodeId'[self]][m'[self]]]
                      /\ pc' = [pc EXCEPT ![self] = "hdl"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << failedAttempts, m, nodeId >>
           /\ UNCHANGED << msgs, nodes, failedMsgs, attemptsPerMsg, 
                           processingsPerMsg >>

hdl(self) == /\ pc[self] = "hdl"
             /\ IF failedAttempts[self] >= MaxFailedAttempts
                   THEN /\ \/ /\ msgs' = msgs \ {m[self]}
                              /\ failedMsgs' = (failedMsgs \cup {m[self]})
                              /\ UNCHANGED attemptsPerMsg
                           \/ /\ attemptsPerMsg' = [attemptsPerMsg EXCEPT ![nodeId[self]][m[self]] = Min(attemptsPerMsg[nodeId[self]][m[self]]+1, MaxFailedAttempts)]
                              /\ UNCHANGED <<msgs, failedMsgs>>
                        /\ pc' = [pc EXCEPT ![self] = "p"]
                        /\ UNCHANGED processingsPerMsg
                   ELSE /\ processingsPerMsg' = [processingsPerMsg EXCEPT ![m[self]] = processingsPerMsg[m[self]] + 1]
                        /\ pc' = [pc EXCEPT ![self] = "ex"]
                        /\ UNCHANGED << msgs, failedMsgs, attemptsPerMsg >>
             /\ UNCHANGED << nodes, failedAttempts, m, nodeId >>

ex(self) == /\ pc[self] = "ex"
            /\ \/ /\ msgs' = msgs \ {m[self]}
                  /\ UNCHANGED attemptsPerMsg
               \/ /\ attemptsPerMsg' = [attemptsPerMsg EXCEPT ![nodeId[self]][m[self]] = Min(attemptsPerMsg[nodeId[self]][m[self]]+1, MaxFailedAttempts)]
                  /\ msgs' = msgs
            /\ pc' = [pc EXCEPT ![self] = "p"]
            /\ UNCHANGED << nodes, failedMsgs, processingsPerMsg, 
                            failedAttempts, m, nodeId >>

Processor(self) == p(self) \/ hdl(self) \/ ex(self)

Next == (\E self \in 1..NProcessors: Processor(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..NProcessors : WF_vars(Processor(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
          
TypeOK == /\ msgs \in SUBSET (1..NMsgs)
          /\ attemptsPerMsg \in [1..NNodes -> [1..NMsgs -> Nat]]
          /\ processingsPerMsg \in [1..NMsgs -> Nat]
                
LowerBoundOnProcessingAttempts == \A msg \in 1..NMsgs : 
                                    (msg \in failedMsgs) => (processingsPerMsg[msg] >= MaxFailedAttempts)                     

UpperBoundOnProcessingAttempts == \A msg \in 1..NMsgs : 
                                    processingsPerMsg[msg] <= MaxFailedAttempts + NProcessors - 1 

=============================================================================
\* Modification History
\* Last modified Sun Feb 05 22:26:34 CET 2017 by Tomasz Masternak
\* Created Sat Feb 04 21:58:56 CET 2017 by Tomasz Masternak
