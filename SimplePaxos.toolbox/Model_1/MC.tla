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
const_1440955931104344000 == 
{c1, c2}
----

\* MV CONSTANT definitions P
const_1440955931114345000 == 
{p1, p2, p3}
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1440955931124346000 ==
0..3
----
\* INIT definition @modelBehaviorInit:0
init_1440955931134347000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_1440955931144348000 ==
Next
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1440955931154349000 ==
[](IsChosen(c1, accepted) => [](\neg IsChosen(c2, accepted)))
----
=============================================================================
\* Modification History
\* Created Sun Aug 30 13:32:11 EDT 2015 by nano
