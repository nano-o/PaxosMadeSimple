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
const_1440955890293338000 == 
{c1, c2}
----

\* MV CONSTANT definitions P
const_1440955890303339000 == 
{p1, p2, p3}
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1440955890314340000 ==
0..3
----
\* INIT definition @modelBehaviorInit:0
init_1440955890324341000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_1440955890334342000 ==
Next
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1440955890344343000 ==
[](IsChosen(c1, accepted) => [](\neg IsChosen(c2, accepted)))
----
=============================================================================
\* Modification History
\* Created Sun Aug 30 13:31:30 EDT 2015 by nano
