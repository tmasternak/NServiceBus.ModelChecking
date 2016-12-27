---- MODULE MC ----
EXTENDS Recoverability, TLC

\* CONSTANT definitions @modelParameterConstants:0M
const_148287297250946000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:1MaxAttempts
const_148287297251947000 == 
2
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_148287297252948000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_148287297253949000 ==
EitherFailedOrProcessed
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_148287297254950000 ==
MessageAttemptedNoMoreThanMax
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_148287297256051000 ==
Termination
----
=============================================================================
\* Modification History
\* Created Tue Dec 27 22:09:32 CET 2016 by Tomasz Masternak
