---- MODULE MC ----
EXTENDS Recoverability, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxAttempts
const_1483445957967167000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1Msgs
const_1483445957977168000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2CacheSize
const_1483445957987169000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3Crashes
const_1483445957998170000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:4Processes
const_1483445958008171000 == 
{1, 2}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1483445958018172000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1483445958028173000 ==
EitherFailedOrProcessed
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1483445958038174000 ==
NoMoreThanMaxAttempts
----
=============================================================================
\* Modification History
\* Created Tue Jan 03 13:19:18 CET 2017 by Tomasz Masternak
