---- MODULE MC ----
EXTENDS SqlServer, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxFailedAttempts
const_1486330006517416000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1NMsgs
const_1486330006527417000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2NProcessors
const_1486330006538418000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:3NNodes
const_1486330006548419000 == 
1
----

\* Constant expression definition @modelExpressionEval
const_expr_1486330006559420000 == 
SUBSET (1..2)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1486330006559420000>>)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1486330006569421000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1486330006579422000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1486330006589423000 ==
UpperBoundOnProcessingAttempts
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1486330006599424000 ==
LowerBoundOnProcessingAttempts
----
=============================================================================
\* Modification History
\* Created Sun Feb 05 22:26:46 CET 2017 by Tomasz Masternak
