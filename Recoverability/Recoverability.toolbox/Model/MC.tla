---- MODULE MC ----
EXTENDS Recoverability, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxAttempts
const_1483306639468197000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:5Msgs
const_1483306639479198000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:7CacheSize
const_1483306639489199000 == 
1
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1483306639500200000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1483306639510201000 ==
EitherFailedOrProcessed
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1483306639520202000 ==
NoMoreThanMaxAttempts
----
=============================================================================
\* Modification History
\* Created Sun Jan 01 22:37:19 CET 2017 by Tomasz Masternak
