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
const_1440962536162509000 == 
{c1, c2}
----

\* MV CONSTANT definitions P
const_1440962536172510000 == 
{p1, p2, p3}
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1440962536183511000 ==
0..3
----
\* INIT definition @modelBehaviorInit:0
init_1440962536193512000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_1440962536203513000 ==
Next
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1440962536213514000 ==
Agreement
----
=============================================================================
\* Modification History
\* Created Sun Aug 30 15:22:16 EDT 2015 by nano
