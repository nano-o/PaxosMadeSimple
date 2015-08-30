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
const_1440954524488307000 == 
{c1, c2}
----

\* MV CONSTANT definitions P
const_1440954524498308000 == 
{p1, p2, p3}
----

\* New definitions @modelParameterNewDefinitions
Init1 ==
/\  accepted = ( p1 :> [number |-> 3, command |-> c1] @@
  p2 :> [number |-> 3, command |-> c1] @@
  p3 :> <<>> )
/\  chosen = {c1}
/\  lastPromise = (p1 :> 2 @@ p2 :> 3 @@ p3 :> 3)
/\  network = { [number |-> 1, type |-> "prepare"],
  [number |-> 2, type |-> "prepare"],
  [number |-> 3, type |-> "prepare"],
  [type |-> "propose", proposal |-> [number |-> 2, command |-> c2]],
  [type |-> "propose", proposal |-> [number |-> 3, command |-> c1]],
  [number |-> 2, type |-> "prepare-response", proposal |-> <<>>, from |-> p1],
  [number |-> 2, type |-> "prepare-response", proposal |-> <<>>, from |-> p2],
  [number |-> 3, type |-> "prepare-response", proposal |-> <<>>, from |-> p2],
  [number |-> 3, type |-> "prepare-response", proposal |-> <<>>, from |-> p3] }
/\  proposalNumber = (p1 :> 1 @@ p2 :> 2 @@ p3 :> 3)
/\  proposedCommand = (p1 :> "none" @@ p2 :> c2 @@ p3 :> c1)
----
\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1440954524508309000 ==
0..3
----
\* INIT definition @modelBehaviorInit:0
init_1440954524518310000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_1440954524529311000 ==
Next
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1440954524539312000 ==
[](IsChosen(c1, accepted) => [](\neg IsChosen(c2, accepted)))
----
=============================================================================
\* Modification History
\* Created Sun Aug 30 13:08:44 EDT 2015 by nano
