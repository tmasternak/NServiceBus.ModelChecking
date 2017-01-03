---- MODULE MC ----
EXTENDS Recoverability, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxAttempts
const_1483448799002343000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:1Msgs
const_1483448799012344000 == 
1..4
----

\* CONSTANT definitions @modelParameterConstants:2CacheSize
const_1483448799022345000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Crashes
const_1483448799032346000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:4Processes
const_1483448799043347000 == 
{1, 2}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1483448799054348000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1483448799064349000 ==
EitherFailedOrProcessed
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1483448799074350000 ==
NoMoreThanMaxAttempts
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1483448799084351000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Tue Jan 03 14:06:39 CET 2017 by Tomasz Masternak
