--------------------------- MODULE Recoverability ---------------------------
EXTENDS Integers, FiniteSets

CONSTANTS M,            \* Set of all possible messages *\
          MaxAttempts   \* Max number of processing attempts *\

ASSUME /\ M \in Nat
       /\ MaxAttempts \in Nat


(*

--fair algorithm ReceiveWithRetries {
    variables input = 1..M, errors = {}, effects = {}, input0 = input,
              attempts = [msg \in input |-> 0];
    {
        while (Cardinality(input) > 0)
        { with (msg \in input)
          {     either  { input := input \ {msg};
                          effects := effects \cup {msg}; }
                or      { if   (attempts[msg] < MaxAttempts) 
                               { attempts := [attempts EXCEPT ![msg] = @ + 1]; } 
                          else { input := input \ {msg};
                                 errors := errors \cup {msg};
                               }
                        }
          }
        }
    } 
} 

*)
\* BEGIN TRANSLATION
VARIABLES input, errors, effects, input0, attempts, pc

vars == << input, errors, effects, input0, attempts, pc >>

Init == (* Global variables *)
        /\ input = 1..M
        /\ errors = {}
        /\ effects = {}
        /\ input0 = input
        /\ attempts = [msg \in input |-> 0]
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF Cardinality(input) > 0
               THEN /\ \E msg \in input:
                         \/ /\ input' = input \ {msg}
                            /\ effects' = (effects \cup {msg})
                            /\ UNCHANGED <<errors, attempts>>
                         \/ /\ IF attempts[msg] < MaxAttempts
                                  THEN /\ attempts' = [attempts EXCEPT ![msg] = @ + 1]
                                       /\ UNCHANGED << input, errors >>
                                  ELSE /\ input' = input \ {msg}
                                       /\ errors' = (errors \cup {msg})
                                       /\ UNCHANGED attempts
                            /\ UNCHANGED effects
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << input, errors, effects, attempts >>
         /\ UNCHANGED input0

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION


EitherFailedOrProcessed == (pc = "Done") => (/\ errors \intersect effects = {}
                                             /\ input0 = errors \cup effects)
                                             
MessageAttemptedNoMoreThanMax == (pc = "Done") => \A msg \in input0: attempts[msg] <= MaxAttempts

=============================================================================
\* Modification History
\* Last modified Tue Dec 27 22:10:08 CET 2016 by Tomasz Masternak
\* Created Tue Dec 27 20:32:15 CET 2016 by Tomasz Masternak
