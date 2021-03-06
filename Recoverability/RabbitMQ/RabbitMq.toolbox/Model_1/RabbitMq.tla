------------------------------ MODULE RabbitMq ------------------------------
EXTENDS Integers, FiniteSets

MaxAttempts == 2

(*
--algorithm Recoverability
{   variables msgs = {1,2,3,4};
    
    fair process (Endpoint \in 1..3)
    variable processed = FALSE, errorHandled = FALSE, deliveryAttempts = 0,
             msg = 0, invocations = 0; 
    {   rcv: with(m \in msgs)
               { msg := m;
                 msgs := msgs \ {m}; 
               };
              
        prc: while(processed # TRUE /\ errorHandled # TRUE)
               { invocations := invocations + 1;
               
                 either { processed := TRUE;}
                 or     { deliveryAttempts := deliveryAttempts + 1;
                          errorHandled := deliveryAttempts >= MaxAttempts; }
               }                   
    }
}

*)
\* BEGIN TRANSLATION
VARIABLES msgs, pc, processed, errorHandled, deliveryAttempts, msg, 
          invocations

vars == << msgs, pc, processed, errorHandled, deliveryAttempts, msg, 
           invocations >>

ProcSet == (1..3)

Init == (* Global variables *)
        /\ msgs = {1,2,3,4}
        (* Process Endpoint *)
        /\ processed = [self \in 1..3 |-> FALSE]
        /\ errorHandled = [self \in 1..3 |-> FALSE]
        /\ deliveryAttempts = [self \in 1..3 |-> 0]
        /\ msg = [self \in 1..3 |-> 0]
        /\ invocations = [self \in 1..3 |-> 0]
        /\ pc = [self \in ProcSet |-> "rcv"]

rcv(self) == /\ pc[self] = "rcv"
             /\ \E m \in msgs:
                  /\ msg' = [msg EXCEPT ![self] = m]
                  /\ msgs' = msgs \ {m}
             /\ pc' = [pc EXCEPT ![self] = "prc"]
             /\ UNCHANGED << processed, errorHandled, deliveryAttempts, 
                             invocations >>

prc(self) == /\ pc[self] = "prc"
             /\ IF processed[self] # TRUE /\ errorHandled[self] # TRUE
                   THEN /\ invocations' = [invocations EXCEPT ![self] = invocations[self] + 1]
                        /\ \/ /\ processed' = [processed EXCEPT ![self] = TRUE]
                              /\ UNCHANGED <<errorHandled, deliveryAttempts>>
                           \/ /\ deliveryAttempts' = [deliveryAttempts EXCEPT ![self] = deliveryAttempts[self] + 1]
                              /\ errorHandled' = [errorHandled EXCEPT ![self] = deliveryAttempts'[self] >= MaxAttempts]
                              /\ UNCHANGED processed
                        /\ pc' = [pc EXCEPT ![self] = "prc"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << processed, errorHandled, 
                                        deliveryAttempts, invocations >>
             /\ UNCHANGED << msgs, msg >>

Endpoint(self) == rcv(self) \/ prc(self)

Next == (\E self \in 1..3: Endpoint(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..3 : WF_vars(Endpoint(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

UpperBoundOnAttempts == \A self \in ProcSet: invocations[self] <= MaxAttempts

=============================================================================
\* Modification History
\* Last modified Sun Feb 05 22:07:14 CET 2017 by Tomasz Masternak
\* Created Sun Feb 05 22:05:47 CET 2017 by Tomasz Masternak
