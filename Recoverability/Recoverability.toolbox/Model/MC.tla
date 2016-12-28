---- MODULE MC ----
EXTENDS Recoverability, TLC

\* CONSTANT definitions @modelParameterConstants:0M
const_14829275841642000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:1MaxAttempts
const_14829275841743000 == 
2
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_14829275841844000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_14829275841945000 ==
EitherFailedOrProcessed
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_14829275842046000 ==
MessageAttemptedNoMoreThanMax
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_14829275842147000 ==
Termination
----
=============================================================================
\* Modification History
\* Created Wed Dec 28 13:19:44 CET 2016 by Tomasz Masternak
