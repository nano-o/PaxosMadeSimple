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
const_1440961039799472000 == 
{c1, c2}
----

\* MV CONSTANT definitions P
const_1440961039809473000 == 
{p1, p2, p3}
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1440961039819474000 ==
0..3
----
\* INIT definition @modelBehaviorInit:0
init_1440961039830475000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_1440961039840476000 ==
Next
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1440961039850477000 ==
TypeInvariant
----
=============================================================================
\* Modification History
\* Created Sun Aug 30 14:57:19 EDT 2015 by nano
