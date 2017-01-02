---- MODULE MC ----
EXTENDS Recoverability, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxAttempts
const_1483365634978136000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1Msgs
const_1483365634988137000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2CacheSize
const_1483365634998138000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3Crashes
const_1483365635008139000 == 
TRUE
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1483365635019140000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1483365635029141000 ==
EitherFailedOrProcessed
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1483365635039142000 ==
NoMoreThanMaxAttempts
----
=============================================================================
\* Modification History
\* Created Mon Jan 02 15:00:35 CET 2017 by Tomasz Masternak
