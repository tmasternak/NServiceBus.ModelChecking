---- MODULE MC ----
EXTENDS Recoverability, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxAttempts
const_1483620600146139000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1Msgs
const_1483620600157140000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2CacheSize
const_1483620600167141000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3Crashes
const_1483620600177142000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:4Processes
const_1483620600187143000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:5TxTimeouts
const_1483620600198144000 == 
FALSE
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1483620600208145000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1483620600218146000 ==
NoMoreThanMaxAttempts
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1483620600228147000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Thu Jan 05 13:50:00 CET 2017 by Tomasz Masternak
