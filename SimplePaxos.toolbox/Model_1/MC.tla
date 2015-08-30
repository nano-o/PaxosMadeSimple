---- MODULE MC ----
EXTENDS SimplePaxos, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3
----

\* MV CONSTANT definitions C
const_1440957715330396000 == 
{c1, c2}
----

\* MV CONSTANT definitions P
const_1440957715340397000 == 
{p1, p2, p3}
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1440957715350398000 ==
0..3
----
\* INIT definition @modelBehaviorInit:0
init_1440957715360399000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_1440957715370400000 ==
Next
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1440957715381401000 ==
TypeInvariant
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1440957715391402000 ==
Cardinality(chosen) <=1
----
=============================================================================
\* Modification History
\* Created Sun Aug 30 14:01:55 EDT 2015 by nano
