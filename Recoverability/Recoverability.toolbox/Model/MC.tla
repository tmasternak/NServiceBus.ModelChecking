---- MODULE MC ----
EXTENDS Recoverability, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxAttempts
const_1483569138562433000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1Msgs
const_1483569138572434000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2CacheSize
const_1483569138582435000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3Crashes
const_1483569138593436000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:4Processes
const_1483569138603437000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:5TxTimeouts
const_1483569138614438000 == 
FALSE
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1483569138624439000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1483569138635440000 ==
NoMoreThanMaxAttempts
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1483569138645441000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Wed Jan 04 23:32:18 CET 2017 by Tomasz Masternak
