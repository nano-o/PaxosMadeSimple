---- MODULE MC ----
EXTENDS PaxosMadeSimple, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT definitions Acceptor
const_172134189577118000 == 
{a1, a2, a3}
----

\* MV CONSTANT definitions Value
const_172134189577119000 == 
{v1, v2}
----

\* SYMMETRY definition
symm_172134189577120000 == 
Permutations(const_172134189577118000) \union Permutations(const_172134189577119000)
----

\* CONSTANT definitions @modelParameterConstants:2Quorum
const_172134189577121000 == 
{Q \in SUBSET Acceptor : 2*Cardinality(Q) > Cardinality(Acceptor)}
----

\* CONSTANT definition @modelParameterDefinitions:1
def_ov_172134189577123000 ==
0..3
----
=============================================================================
\* Modification History
\* Created Thu Jul 18 15:31:35 PDT 2024 by nano
