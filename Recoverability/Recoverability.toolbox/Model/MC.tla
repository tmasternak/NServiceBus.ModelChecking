---- MODULE MC ----
EXTENDS Recoverability, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxAttempts
const_148335705701695000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:5Msgs
const_148335705702696000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:7CacheSize
const_148335705703797000 == 
3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_148335705704798000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_148335705705799000 ==
EitherFailedOrProcessed
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1483357057067100000 ==
NoMoreThanMaxAttempts
----
=============================================================================
\* Modification History
\* Created Mon Jan 02 12:37:37 CET 2017 by Tomasz Masternak
