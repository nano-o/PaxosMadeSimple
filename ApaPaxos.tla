---------- MODULE ApaPaxos ----------

Acceptor == {"A1_OF_ACCEPTOR", "A2_OF_ACCEPTOR", "A3_OF_ACCEPTOR"}
Value == {"V1_OF_VALUE", "V2_OF_VALUE"}
Quorum == {{"A1_OF_ACCEPTOR", "A2_OF_ACCEPTOR"}, {"A1_OF_ACCEPTOR", "A3_OF_ACCEPTOR"}, {"A2_OF_ACCEPTOR", "A3_OF_ACCEPTOR"}}
\* We also need to substitue some operators and we have to do the in a TLC cfg file

ApaBallot == {0,1,2,3,4}
ApaSomeValue == "V1_OF_VALUE"

VARIABLES 
    \* @type: ACCEPTOR -> Int;
    maxBal,
    \* @type: ACCEPTOR -> Int;
    maxVBal,
    \* @type: ACCEPTOR -> VALUE;
    maxVVal,
    \* @type: Set(Int);
    1aMsgs,
    \* @type: Set({acc : ACCEPTOR, bal : Int, mbal : Int, mval : VALUE});
    1bMsgs,
    \* @type: Set({bal : Int, val : VALUE});
    2aMsgs,
    \* @type: Set({acc : ACCEPTOR, bal : Int, val : VALUE});
    2bMsgs

INSTANCE Paxos

NoFutureVote == \A m \in 2bMsgs : m.bal <= maxBal[m.acc]
OneVotePerBallot == \A m1,m2 \in 2aMsgs : m1.bal = m2.bal => m1 = m2
OneValuePerBallot == \A m1,m2 \in 2bMsgs : m1.bal = m2.bal => m1.val = m2.val
VoteForProposal == \A m1 \in 2bMsgs : \E m2 \in 2aMsgs : m1.bal = m2.bal /\ m1.val = m2.val

Invariant1 == 
    /\  OneVotePerBallot
    /\  VoteForProposal
    /\  OneValuePerBallot
    /\  NoFutureVote
Invariant1_ == TypeOK /\ Invariant1

===============================================