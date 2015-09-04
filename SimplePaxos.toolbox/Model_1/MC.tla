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
const_1441298565319230000 == 
{c1, c2}
----

\* MV CONSTANT definitions P
const_1441298565330231000 == 
{p1, p2, p3}
----

\* SYMMETRY definition
symm_1441298565340232000 == 
Permutations(const_1441298565319230000) \union Permutations(const_1441298565330231000)
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1441298565350233000 ==
0..4
----
\* CONSTRAINT definition @modelParameterContraint:0
constr_1441298565360234000 ==
proposalNumber[p3] >= proposalNumber[p2] /\ proposalNumber[p3] >= proposalNumber[p1] /\ proposalNumber[p2] >= proposalNumber[p1]
/\ (\E p \in P : accepted[p] # <<>> /\ accepted[p].number = proposalNumber[p1] => \A q \in P : accepted[q] # <<>> /\ accepted[q].number = proposalNumber[p2] => accepted[q].command # accepted[p].command)
----
\* INIT definition @modelBehaviorInit:0
init_1441298565370235000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_1441298565380236000 ==
Next
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1441298565390237000 ==
Cardinality(chosen) <= 1
----
=============================================================================
\* Modification History
\* Created Thu Sep 03 12:42:45 EDT 2015 by nano
