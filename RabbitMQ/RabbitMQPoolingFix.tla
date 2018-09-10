------------------------- MODULE RabbitMQPoolingFix -------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANTS MaxSeqNo

(* --algorithm rabbitmq_channel_pooling

variables 

channel = [
    PendingTasks |-> {}, 
    InPool       |-> FALSE,
    Client       |-> 
    [
        IsOpen         |-> FALSE,
        NextSequenceNo |-> 0
    ]
];

process RabbitClient = 2
begin RC:
    while TRUE do
        if channel.Client.IsOpen = TRUE then
            channel.Client.IsOpen := FALSE;
        Clear_On_Shutdown:
            channel.PendingTasks := {};
        else
            channel.Client.IsOpen := TRUE || channel.Client.NextSequenceNo := 1;
        Clear_On_Recovery:
            channel.PendingTasks := {};
        end if;
    end while;
end process;

process Transport = 1
variables tcs = 0;
begin P:
  while TRUE do
    Get_Channel:
      if channel.Client.IsOpen = FALSE then
        channel.Client := [ IsOpen |-> TRUE, NextSequenceNo |-> 1] ||
        channel.PendingTasks := {} ||
        channel.InPool := FALSE;
      else 
        channel.InPool := FALSE;
      end if;
      
    Create_Tcs:
      tcs := channel.Client.NextSequenceNo;
      
    Store_Tcs:
      channel.PendingTasks := channel.PendingTasks \union {tcs};
      
    Send_Message:
      either
        if channel.Client.NextSequenceNo <= MaxSeqNo then
            channel.Client.NextSequenceNo := channel.Client.NextSequenceNo + 1;
        end if;
      or
        skip;
      end either; 
    
    Release_Channel:
      if channel.Client.IsOpen = FALSE then
        channel.Client := [IsOpen |-> FALSE, NextSequenceNo |-> 0] ||
        channel.PendingTasks := {} ||
        channel.InPool := FALSE;
      else
        channel.InPool := TRUE;
      end if;
      
  end while;
end process;
     

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES channel, pc, tcs

vars == << channel, pc, tcs >>

ProcSet == {2} \cup {1}

Init == (* Global variables *)
        /\ channel =           [
                         PendingTasks |-> {},
                         InPool       |-> FALSE,
                         Client       |->
                         [
                             IsOpen         |-> FALSE,
                             NextSequenceNo |-> 0
                         ]
                     ]
        (* Process Transport *)
        /\ tcs = 0
        /\ pc = [self \in ProcSet |-> CASE self = 2 -> "RC"
                                        [] self = 1 -> "P"]

RC == /\ pc[2] = "RC"
      /\ IF channel.Client.IsOpen = TRUE
            THEN /\ channel' = [channel EXCEPT !.Client.IsOpen = FALSE]
                 /\ pc' = [pc EXCEPT ![2] = "Clear_On_Shutdown"]
            ELSE /\ channel' = [channel EXCEPT !.Client.IsOpen = TRUE,
                                               !.Client.NextSequenceNo = 1]
                 /\ pc' = [pc EXCEPT ![2] = "Clear_On_Recovery"]
      /\ tcs' = tcs

Clear_On_Shutdown == /\ pc[2] = "Clear_On_Shutdown"
                     /\ channel' = [channel EXCEPT !.PendingTasks = {}]
                     /\ pc' = [pc EXCEPT ![2] = "RC"]
                     /\ tcs' = tcs

Clear_On_Recovery == /\ pc[2] = "Clear_On_Recovery"
                     /\ channel' = [channel EXCEPT !.PendingTasks = {}]
                     /\ pc' = [pc EXCEPT ![2] = "RC"]
                     /\ tcs' = tcs

RabbitClient == RC \/ Clear_On_Shutdown \/ Clear_On_Recovery

P == /\ pc[1] = "P"
     /\ pc' = [pc EXCEPT ![1] = "Get_Channel"]
     /\ UNCHANGED << channel, tcs >>

Get_Channel == /\ pc[1] = "Get_Channel"
               /\ IF channel.Client.IsOpen = FALSE
                     THEN /\ channel' = [channel EXCEPT !.Client = [ IsOpen |-> TRUE, NextSequenceNo |-> 1],
                                                        !.PendingTasks = {},
                                                        !.InPool = FALSE]
                     ELSE /\ channel' = [channel EXCEPT !.InPool = FALSE]
               /\ pc' = [pc EXCEPT ![1] = "Create_Tcs"]
               /\ tcs' = tcs

Create_Tcs == /\ pc[1] = "Create_Tcs"
              /\ tcs' = channel.Client.NextSequenceNo
              /\ pc' = [pc EXCEPT ![1] = "Store_Tcs"]
              /\ UNCHANGED channel

Store_Tcs == /\ pc[1] = "Store_Tcs"
             /\ channel' = [channel EXCEPT !.PendingTasks = channel.PendingTasks \union {tcs}]
             /\ pc' = [pc EXCEPT ![1] = "Send_Message"]
             /\ tcs' = tcs

Send_Message == /\ pc[1] = "Send_Message"
                /\ \/ /\ IF channel.Client.NextSequenceNo <= MaxSeqNo
                            THEN /\ channel' = [channel EXCEPT !.Client.NextSequenceNo = channel.Client.NextSequenceNo + 1]
                            ELSE /\ TRUE
                                 /\ UNCHANGED channel
                   \/ /\ TRUE
                      /\ UNCHANGED channel
                /\ pc' = [pc EXCEPT ![1] = "Release_Channel"]
                /\ tcs' = tcs

Release_Channel == /\ pc[1] = "Release_Channel"
                   /\ IF channel.Client.IsOpen = FALSE
                         THEN /\ channel' = [channel EXCEPT !.Client = [IsOpen |-> FALSE, NextSequenceNo |-> 0],
                                                            !.PendingTasks = {},
                                                            !.InPool = FALSE]
                         ELSE /\ channel' = [channel EXCEPT !.InPool = TRUE]
                   /\ pc' = [pc EXCEPT ![1] = "P"]
                   /\ tcs' = tcs

Transport == P \/ Get_Channel \/ Create_Tcs \/ Store_Tcs \/ Send_Message
                \/ Release_Channel

Next == RabbitClient \/ Transport

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

NoPooledChannelHasCorruptedState == (channel.Client.IsOpen /\ channel.InPool /\ pc[2] /= "Clear_On_Recovery") 
                                     => \A t \in channel.PendingTasks : t <= channel.Client.NextSequenceNo

=============================================================================
\* Modification History
\* Last modified Mon Sep 10 11:08:12 CEST 2018 by Tomasz Masternak
\* Created Fri Sep 07 11:25:52 CEST 2018 by Tomasz Masternak
