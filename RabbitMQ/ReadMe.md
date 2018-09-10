## Overview

This folder holds two specifications for parts of RabbitMQ transport dealing wiht publisher confirmns and auto-recoverability feature. It models interaction between [MessageDispatcher](https://github.com/Particular/NServiceBus.RabbitMQ/blob/a386c5ffede50c841788d8c2426fe0da40895186/src/NServiceBus.Transport.RabbitMQ/Sending/MessageDispatcher.cs), [ConfirmAwareChannel](https://github.com/Particular/NServiceBus.RabbitMQ/blob/a386c5ffede50c841788d8c2426fe0da40895186/src/NServiceBus.Transport.RabbitMQ/Connection/ConfirmsAwareChannel.cs) and RabbitMQ client library.

The first specification `RabbitMQPoolingFix.tla` show an approach when messages collection is cleared only in the callbacks. The second one changes it to make additional clean-up when getting channel from the pool and receiving it from there.

The model checks the fallowing invariant:

```
NoPooledChannelHasCorruptedState == (channel.Client.IsOpen /\ channel.InPool /\ pc[2] /= "Clear_On_Recovery") 
                                     => \A t \in channel.PendingTasks : t <= channel.Client.NextSequenceNo
```

Which in loose transation means that if a channel is in the pool, is opened and there is no outstainding execution of recoverability reconnection callback than there will be no element in the messages collection that will have number grater than `NextSequenceNo` of the underlying channel.


## Failing behavior

Here is a sample failing behavior of the first specification:

```
1: <Initial predicate>
/\ channel = [ PendingTasks |-> {},
  InPool |-> FALSE,
  Client |-> [IsOpen |-> FALSE, NextSequenceNo |-> 0] ]
/\ tcs = 0
/\ pc = <<"P", "RC">>

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
2: <RC line 99, col 7 to line 106, col 19 of module RabbitMQPoolingFix>
/\ channel = [ PendingTasks |-> {},
  InPool |-> FALSE,
  Client |-> [IsOpen |-> TRUE, NextSequenceNo |-> 1] ]
/\ tcs = 0
/\ pc = <<"P", "Clear_On_Recovery">>

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
3: <P line 120, col 6 to line 122, col 36 of module RabbitMQPoolingFix>
/\ channel = [ PendingTasks |-> {},
  InPool |-> FALSE,
  Client |-> [IsOpen |-> TRUE, NextSequenceNo |-> 1] ]
/\ tcs = 0
/\ pc = <<"Get_Channel", "Clear_On_Recovery">>

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
4: <Clear_On_Recovery line 113, col 22 to line 116, col 34 of module RabbitMQPoolingFix>
/\ channel = [ PendingTasks |-> {},
  InPool |-> FALSE,
  Client |-> [IsOpen |-> TRUE, NextSequenceNo |-> 1] ]
/\ tcs = 0
/\ pc = <<"Get_Channel", "RC">>

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
5: <RC line 99, col 7 to line 106, col 19 of module RabbitMQPoolingFix>
/\ channel = [ PendingTasks |-> {},
  InPool |-> FALSE,
  Client |-> [IsOpen |-> FALSE, NextSequenceNo |-> 1] ]
/\ tcs = 0
/\ pc = <<"Get_Channel", "Clear_On_Shutdown">>

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
6: <Get_Channel line 124, col 16 to line 131, col 28 of module RabbitMQPoolingFix>
/\ channel = [ PendingTasks |-> {},
  InPool |-> FALSE,
  Client |-> [IsOpen |-> TRUE, NextSequenceNo |-> 1] ]
/\ tcs = 0
/\ pc = <<"Create_Tcs", "Clear_On_Shutdown">>

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
7: <Create_Tcs line 133, col 15 to line 136, col 34 of module RabbitMQPoolingFix>
/\ channel = [ PendingTasks |-> {},
  InPool |-> FALSE,
  Client |-> [IsOpen |-> TRUE, NextSequenceNo |-> 1] ]
/\ tcs = 1
/\ pc = <<"Store_Tcs", "Clear_On_Shutdown">>

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
8: <Store_Tcs line 138, col 14 to line 141, col 26 of module RabbitMQPoolingFix>
/\ channel = [ PendingTasks |-> {1},
  InPool |-> FALSE,
  Client |-> [IsOpen |-> TRUE, NextSequenceNo |-> 1] ]
/\ tcs = 1
/\ pc = <<"Send_Message", "Clear_On_Shutdown">>

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
9: <Clear_On_Shutdown line 108, col 22 to line 111, col 34 of module RabbitMQPoolingFix>
/\ channel = [ PendingTasks |-> {},
  InPool |-> FALSE,
  Client |-> [IsOpen |-> TRUE, NextSequenceNo |-> 1] ]
/\ tcs = 1
/\ pc = <<"Send_Message", "RC">>

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
10: <Send_Message line 143, col 17 to line 151, col 29 of module RabbitMQPoolingFix>
/\ channel = [ PendingTasks |-> {},
  InPool |-> FALSE,
  Client |-> [IsOpen |-> TRUE, NextSequenceNo |-> 2] ]
/\ tcs = 1
/\ pc = <<"Release_Channel", "RC">>

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
11: <Release_Channel line 153, col 20 to line 160, col 32 of module RabbitMQPoolingFix>
/\ channel = [ PendingTasks |-> {},
  InPool |-> TRUE,
  Client |-> [IsOpen |-> TRUE, NextSequenceNo |-> 2] ]
/\ tcs = 1
/\ pc = <<"P", "RC">>

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
12: <P line 120, col 6 to line 122, col 36 of module RabbitMQPoolingFix>
/\ channel = [ PendingTasks |-> {},
  InPool |-> TRUE,
  Client |-> [IsOpen |-> TRUE, NextSequenceNo |-> 2] ]
/\ tcs = 1
/\ pc = <<"Get_Channel", "RC">>

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
13: <Get_Channel line 124, col 16 to line 131, col 28 of module RabbitMQPoolingFix>
/\ channel = [ PendingTasks |-> {},
  InPool |-> FALSE,
  Client |-> [IsOpen |-> TRUE, NextSequenceNo |-> 2] ]
/\ tcs = 1
/\ pc = <<"Create_Tcs", "RC">>

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
14: <RC line 99, col 7 to line 106, col 19 of module RabbitMQPoolingFix>
/\ channel = [ PendingTasks |-> {},
  InPool |-> FALSE,
  Client |-> [IsOpen |-> FALSE, NextSequenceNo |-> 2] ]
/\ tcs = 1
/\ pc = <<"Create_Tcs", "Clear_On_Shutdown">>

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
15: <Create_Tcs line 133, col 15 to line 136, col 34 of module RabbitMQPoolingFix>
/\ channel = [ PendingTasks |-> {},
  InPool |-> FALSE,
  Client |-> [IsOpen |-> FALSE, NextSequenceNo |-> 2] ]
/\ tcs = 2
/\ pc = <<"Store_Tcs", "Clear_On_Shutdown">>

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
16: <Clear_On_Shutdown line 108, col 22 to line 111, col 34 of module RabbitMQPoolingFix>
/\ channel = [ PendingTasks |-> {},
  InPool |-> FALSE,
  Client |-> [IsOpen |-> FALSE, NextSequenceNo |-> 2] ]
/\ tcs = 2
/\ pc = <<"Store_Tcs", "RC">>

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
17: <RC line 99, col 7 to line 106, col 19 of module RabbitMQPoolingFix>
/\ channel = [ PendingTasks |-> {},
  InPool |-> FALSE,
  Client |-> [IsOpen |-> TRUE, NextSequenceNo |-> 1] ]
/\ tcs = 2
/\ pc = <<"Store_Tcs", "Clear_On_Recovery">>

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
18: <Clear_On_Recovery line 113, col 22 to line 116, col 34 of module RabbitMQPoolingFix>
/\ channel = [ PendingTasks |-> {},
  InPool |-> FALSE,
  Client |-> [IsOpen |-> TRUE, NextSequenceNo |-> 1] ]
/\ tcs = 2
/\ pc = <<"Store_Tcs", "RC">>

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
19: <Store_Tcs line 138, col 14 to line 141, col 26 of module RabbitMQPoolingFix>
/\ channel = [ PendingTasks |-> {2},
  InPool |-> FALSE,
  Client |-> [IsOpen |-> TRUE, NextSequenceNo |-> 1] ]
/\ tcs = 2
/\ pc = <<"Send_Message", "RC">>

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
20: <Send_Message line 143, col 17 to line 151, col 29 of module RabbitMQPoolingFix>
/\ channel = [ PendingTasks |-> {2},
  InPool |-> FALSE,
  Client |-> [IsOpen |-> TRUE, NextSequenceNo |-> 1] ]
/\ tcs = 2
/\ pc = <<"Release_Channel", "RC">>

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
21: <Release_Channel line 153, col 20 to line 160, col 32 of module RabbitMQPoolingFix>
/\ channel = [ PendingTasks |-> {2},
  InPool |-> TRUE,
  Client |-> [IsOpen |-> TRUE, NextSequenceNo |-> 1] ]
/\ tcs = 2
/\ pc = <<"P", "RC">>
```
