------------ MODULE Paxos ------------

EXTENDS Integers, FiniteSets, TLC

CONSTANT Value, Acceptor, Quorum

Ballot ==  Nat

SomeValue == CHOOSE v \in Value : TRUE

VARIABLES maxBal, maxVBal, maxVVal,
    1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs,
    rcvd1aMsgs, rcvd1bMsgs, rcvd2aMsgs, rcvd2bMsgs

vars == << maxBal, maxVBal, maxVVal, 1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs, rcvd1aMsgs, rcvd1bMsgs, rcvd2aMsgs, rcvd2bMsgs >>

ShowsSafeAt(Q, b, v) ==
  LET Q1b == {m \in rcvd1bMsgs : m.bal = b /\ m.acc \in Q}
  IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
      /\ \/ \A m \in Q1b : m.mbal = -1
         \/ \E m \in Q1b :
            /\ m.mval = v
            /\ \A m1 \in Q1b : m1.mbal <= m.mbal

Init ==
    /\ maxBal = [a \in Acceptor |-> -1]
    /\ maxVBal = [a \in Acceptor |-> -1]
    /\ maxVVal = [a \in Acceptor |-> SomeValue]
    /\ 1aMsgs = {}
    /\ 1bMsgs = {}
    /\ 2aMsgs = {}
    /\ 2bMsgs = {}
    /\ rcvd1aMsgs = [a \in Acceptor |-> {}]
    /\ rcvd1bMsgs = {} \* received by ballot leaders; no need for a function because they contain the ballot already
    /\ rcvd2aMsgs = [a \in Acceptor |-> {}]
    /\ rcvd2bMsgs = [a \in Acceptor |-> {}]

Phase1a(b) ==
    /\ 1aMsgs' = 1aMsgs \cup {b}
    /\ UNCHANGED <<maxBal, maxVBal, maxVVal, 1bMsgs, 2aMsgs, 2bMsgs, rcvd1aMsgs, rcvd1bMsgs, rcvd2aMsgs, rcvd2bMsgs>>

Receive1aMsg(a, b) ==
    /\ b \in 1aMsgs
    /\ rcvd1aMsgs' = [rcvd1aMsgs EXCEPT ![a] = @ \cup {b}]
    /\ UNCHANGED <<maxBal, maxVBal, maxVVal, 1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs, rcvd1bMsgs, rcvd2aMsgs, rcvd2bMsgs>>

Phase1b(a, b) == 
    /\ b > maxBal[a] /\ b \in rcvd1aMsgs[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ 1bMsgs' = 1bMsgs \cup {[acc |-> a, bal |-> b, mbal |-> maxVBal[a], mval |-> maxVVal[a]]}
    /\ UNCHANGED <<maxVBal, maxVVal, 1aMsgs, 2bMsgs, 2aMsgs, rcvd1aMsgs, rcvd1bMsgs, rcvd2aMsgs, rcvd2bMsgs>>

Receive1bMsg(a, b, mbal, mval) ==
    /\  LET m == [acc |-> a, bal |-> b, mbal |-> mbal, mval |-> mval]
        IN  m \in 1bMsgs /\ rcvd1bMsgs' = rcvd1bMsgs \cup {m}
    /\ UNCHANGED <<maxBal, maxVBal, maxVVal, 1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs, rcvd1aMsgs, rcvd2aMsgs, rcvd2bMsgs>>

Phase2a(b, v) ==
    /\ \A m \in 2aMsgs : m.bal # b
    /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v)
    /\ 2aMsgs' = 2aMsgs \cup {[bal |-> b, val |-> v]}
    /\ UNCHANGED <<1aMsgs, 1bMsgs, maxBal, maxVBal, maxVVal, 2bMsgs, rcvd1aMsgs, rcvd1bMsgs, rcvd2aMsgs, rcvd2bMsgs>>

Receive2aMsg(a, b, v) ==
    /\ [bal |-> b, val |-> v] \in 2aMsgs
    /\ rcvd2aMsgs' = [rcvd2aMsgs EXCEPT ![a] = @ \cup {[bal |-> b, val |-> v]}]
    /\ UNCHANGED <<maxBal, maxVBal, maxVVal, 1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs, rcvd1aMsgs, rcvd1bMsgs, rcvd2bMsgs>>

Phase2b(a, b, v) ==
    /\ b \geq maxBal[a]
    /\ \E m \in rcvd2aMsgs[a] :
        /\ m.bal = b
        /\ maxBal' = [maxBal EXCEPT ![a] = b]
        /\ maxVBal' = [maxVBal EXCEPT ![a] = b]
        /\ maxVVal' = [maxVVal EXCEPT ![a] = m.val]
        /\ 2bMsgs' = 2bMsgs \cup {[acc |-> a, bal |-> b, val |-> m.val]}
    /\ UNCHANGED <<1aMsgs, 1bMsgs, 2aMsgs, rcvd1aMsgs, rcvd1bMsgs, rcvd2aMsgs, rcvd2bMsgs>>

Receive2bMsg(a1, a2, b, v) ==
    /\ [acc |-> a2, bal |-> b, val |-> v] \in 2bMsgs
    /\ rcvd2bMsgs' = [rcvd2bMsgs EXCEPT ![a1] = @ \cup {[acc |-> a2, bal |-> b, val |-> v]}]
    /\ UNCHANGED <<maxBal, maxVBal, maxVVal, 1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs, rcvd1aMsgs, rcvd1bMsgs, rcvd2aMsgs>>

Next == \E b \in Ballot, v \in Value, a \in Acceptor :
    \/ Phase1a(b)
    \/ Receive1aMsg(a, b)
    \/ Phase1b(a, b)
    \/ \E mbal \in Ballot : Receive1bMsg(a, b, mbal, v)
    \/ Phase2a(b, v)
    \/ Receive2aMsg(a, b, v)
    \/ Phase2b(a, b, v)
    \/ \E a2 \in Acceptor : Receive2bMsg(a, a2, b, v)

Spec == Init /\ [][Next]_vars

TypeOK == /\ maxBal  \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVVal \in [Acceptor -> Value \cup {SomeValue}]
          /\ 1aMsgs \in SUBSET Ballot
          /\ 1bMsgs \in SUBSET [acc : Acceptor, bal : Ballot, mbal : Ballot \cup {-1}, mval : Value]
          /\ 2aMsgs \in SUBSET [bal : Ballot, val : Value]
          /\ 2bMsgs \in SUBSET [acc : Acceptor, bal : Ballot, val : Value]
          /\ rcvd1aMsgs \in [Acceptor -> SUBSET Ballot]
          /\ rcvd1bMsgs \in SUBSET [acc : Acceptor, bal : Ballot, mbal : Ballot \cup {-1}, mval : Value]
          /\ rcvd2aMsgs \in [Acceptor -> SUBSET [bal : Ballot, val : Value]]
          /\ rcvd2bMsgs \in [Acceptor -> SUBSET [acc : Acceptor, bal : Ballot, val : Value]]

ChosenIn(b, v) ==
    \E a0 \in Acceptor : \E Q \in Quorum : \A a \in Q : 
        \E m \in rcvd2bMsgs[a0] :
            /\  m.bal = b
            /\  m.acc = a
            /\  m.val = v
                      
Chosen(v) == \E b \in Ballot : ChosenIn(b,v)

Correctness ==
    \A v1,v2 \in Value : Chosen(v1) /\ Chosen(v2) => v1 = v2

THEOREM Spec => []Correctness

NoFutureVote == \A m \in 2bMsgs : m.bal <= maxVBal[m.acc]
OneVotePerBallot == \A m1,m2 \in 2aMsgs : m1.bal = m2.bal => m1 = m2
OneValuePerBallot == \A m1,m2 \in 2bMsgs : m1.bal = m2.bal => m1.val = m2.val
VoteForProposal == \A m1 \in 2bMsgs : \E m2 \in 2aMsgs : m1.bal = m2.bal /\ m1.val = m2.val

TypeOK_ == TypeOK

Invariant0 == \A a \in Acceptor : \A b \in Ballot :
    /\ b \in rcvd1aMsgs[a] => b \in 1aMsgs
    /\ \A v \in Value : [bal |-> b, val |-> v] \in rcvd2aMsgs[a] => [bal |-> b, val |-> v] \in 2aMsgs
    /\ \A a2 \in Acceptor : \A v \in Value : [acc |-> a2, bal |-> b, val |-> v] \in rcvd2bMsgs[a] => [acc |-> a2, bal |-> b, val |-> v] \in 2bMsgs
    /\ \A m \in rcvd1bMsgs : m \in 1bMsgs
Invariant0_ == TypeOK /\ Invariant0

Invariant1 == 
    /\  OneVotePerBallot
    /\  VoteForProposal
    /\  OneValuePerBallot
    /\  NoFutureVote
    /\  \A a \in Acceptor :
          /\ maxVBal[a] <= maxBal[a]
          /\ maxVBal[a] # -1 => [acc |-> a, bal |-> maxVBal[a], val |-> maxVVal[a]] \in 2bMsgs
    /\  \A m \in 2bMsgs : m.bal = maxVBal[m.acc] => m.val = maxVVal[m.acc]
    /\  \A m \in 1bMsgs :
        /\ m.mbal < m.bal
        /\ m.bal <= maxBal[m.acc]
        /\ m.mbal <= maxVBal[m.acc]
        /\ m.mbal = maxVBal[m.acc] => m.mval = maxVVal[m.acc]
        /\ m.mbal # -1 => [acc |-> m.acc, bal |-> m.mbal, val |-> m.mval] \in 2bMsgs
        /\ \A m2b \in 2bMsgs : m2b.acc = m.acc => 
              /\ \neg (m.mbal < m2b.bal /\ m2b.bal < m.bal)
              /\ m2b.bal = m.mbal => m2b.val = m.mval
Invariant1_ == TypeOK /\ Invariant0 /\ Invariant1

Choosable(b, v, Q) ==
    \A a \in Q :
        \/ [acc |-> a, bal |-> b, val |-> v] \in 2bMsgs
        \/ /\ maxBal[a] <= b
           /\ maxVBal[a] < b
           
SafeAt(v, b) ==
    \A Q \in Quorum : \A w \in Value : \A c \in Ballot :
        c < b /\ Choosable(c, w, Q) => v = w

Invariant2 == \A m \in 2aMsgs :
    SafeAt(m.val, m.bal)
Invariant2_ == TypeOK /\ Invariant0 /\ Invariant1 /\ Invariant2    

Correctness_ == TypeOK /\ Invariant0 /\ Invariant1 /\ Invariant2

======================================