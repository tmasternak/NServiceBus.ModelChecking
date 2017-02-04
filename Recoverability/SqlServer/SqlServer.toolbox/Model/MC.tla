---- MODULE MC ----
EXTENDS SqlServer, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxFailedAttempts
const_1486249402351177000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1NMsgs
const_1486249402362178000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2NProcessors
const_1486249402372179000 == 
4
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1486249402382180000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1486249402392181000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1486249402402182000 ==
ProcessingAttemptsAreBounded
----
=============================================================================
\* Modification History
\* Created Sun Feb 05 00:03:22 CET 2017 by Tomasz Masternak
