------------ MODULE Paxos ------------

EXTENDS Integers, FiniteSets, TLC

CONSTANT Value, Acceptor, Quorum

Ballot ==  Nat

SomeValue == CHOOSE v \in Value : TRUE

VARIABLES maxBal, maxVBal, maxVVal, 1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs

vars == << maxBal, maxVBal, maxVVal, 1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs >>

ShowsSafeAt(Q, b, v) ==
  LET Q1b == {m \in 1bMsgs : m.bal = b /\ m.acc \in Q}
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

Phase1a(b) ==
    /\ 1aMsgs' = 1aMsgs \cup {b}
    /\ UNCHANGED <<maxBal, maxVBal, maxVVal, 1bMsgs, 2aMsgs, 2bMsgs>>

Phase1b(a, b) == 
    /\ b > maxBal[a] /\ b \in 1aMsgs
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ 1bMsgs' = 1bMsgs \cup {[acc |-> a, bal |-> b, mbal |-> maxVBal[a], mval |-> maxVVal[a]]}
    /\ UNCHANGED <<maxVBal, maxVVal, 1aMsgs, 2bMsgs, 2aMsgs>>

Phase2a(b, v) ==
    /\ \A m \in 2aMsgs : m.bal # b
    /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v)
    /\ 2aMsgs' = 2aMsgs \cup {[bal |-> b, val |-> v]}
    /\ UNCHANGED <<1aMsgs, 1bMsgs, maxBal, maxVBal, maxVVal, 2bMsgs>>

Phase2b(a, b, v) ==
    /\ b \geq maxBal[a]
    /\ \E m \in 2aMsgs :
        /\ m.bal = b
        /\ maxBal' = [maxBal EXCEPT ![a] = b]
        /\ maxVBal' = [maxVBal EXCEPT ![a] = b]
        /\ maxVVal' = [maxVVal EXCEPT ![a] = m.val]
        /\ 2bMsgs' = 2bMsgs \cup {[acc |-> a, bal |-> b, val |-> m.val]}
    /\ UNCHANGED <<1aMsgs, 1bMsgs, 2aMsgs>>

Next == \E b \in Ballot, v \in Value, a \in Acceptor :
    \/ Phase1a(b)
    \/ Phase1b(a, b)
    \/ Phase2a(b, v)
    \/ Phase2b(a, b, v)

Spec == Init /\ [][Next]_vars

TypeOK == /\ maxBal  \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVVal \in [Acceptor -> Value \cup {SomeValue}]
          /\ 1aMsgs \in SUBSET Ballot
          /\ 1bMsgs \in SUBSET [acc : Acceptor, bal : Ballot, mbal : Ballot \cup {-1}, mval : Value]
          /\ 2aMsgs \in SUBSET [bal : Ballot, val : Value]
          /\ 2bMsgs \in SUBSET [acc : Acceptor, bal : Ballot, val : Value]

ChosenIn(b, v) ==
    \E Q \in Quorum : \A a \in Q : 
        \E m \in 2bMsgs :
            /\  m.bal = b
            /\  m.acc = a
            /\  m.val = v
                      
Chosen(v) == \E b \in Ballot : ChosenIn(b,v)

Correctness ==
    \A v1,v2 \in Value : Chosen(v1) /\ Chosen(v2) => v1 = v2

THEOREM Spec => []Correctness

======================================
