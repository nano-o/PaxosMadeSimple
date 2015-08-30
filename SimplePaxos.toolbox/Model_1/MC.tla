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
const_1440959768709433000 == 
{c1, c2}
----

\* MV CONSTANT definitions P
const_1440959768719434000 == 
{p1, p2, p3}
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1440959768729435000 ==
0..3
----
\* INIT definition @modelBehaviorInit:0
init_1440959768740436000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_1440959768750437000 ==
Next
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1440959768760438000 ==
Agreement
----
=============================================================================
\* Modification History
\* Created Sun Aug 30 14:36:08 EDT 2015 by nano
