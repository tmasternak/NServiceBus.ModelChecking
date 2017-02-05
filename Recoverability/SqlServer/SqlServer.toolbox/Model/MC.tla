---- MODULE MC ----
EXTENDS SqlServer, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxFailedAttempts
const_1486328458556366000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1NMsgs
const_1486328458567367000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2NProcessors
const_1486328458577368000 == 
4
----

\* Constant expression definition @modelExpressionEval
const_expr_1486328458587369000 == 
SUBSET (1..2)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1486328458587369000>>)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1486328458597370000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1486328458608371000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1486328458618372000 ==
UpperBoundOnProcessingAttempts
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1486328458629373000 ==
LowerBoundOnProcessingAttempts
----
=============================================================================
\* Modification History
\* Created Sun Feb 05 22:00:58 CET 2017 by Tomasz Masternak
