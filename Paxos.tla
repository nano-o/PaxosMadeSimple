------------ MODULE Paxos ------------

\* TODO: we have to do everything in the receive actions, because for liveness nodes need to act on what they receive in a timely way.

EXTENDS Integers, FiniteSets, TLC

CONSTANT Value, Acceptor, Quorum, MaxBallot, MaxTime

Ballot ==  0..MaxBallot

Time == -1..MaxTime

SomeValue == CHOOSE v \in Value : TRUE

VARIABLES maxBal, maxVBal, maxVVal,
    1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs,
    rcvd1aMsgs, rcvd1bMsgs, rcvd2aMsgs, rcvd2bMsgs,
    clock

vars == << maxBal, maxVBal, maxVVal, 1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs, rcvd1aMsgs, rcvd1bMsgs, rcvd2aMsgs, rcvd2bMsgs, clock >>

ShowsSafeAt(Q, b, v) ==
  LET Q1b == {m \in rcvd1bMsgs : m[2].bal = b /\ m[2].acc \in Q}
  IN  /\ \A a \in Q : \E m \in Q1b : m[2].acc = a
      /\ \/ \A m \in Q1b : m[2].mbal = -1
         \/ \E m \in Q1b :
            /\ m[2].mval = v
            /\ \A m1 \in Q1b : m1[2].mbal <= m[2].mbal

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
    /\ clock = -1 \* the clock is started by setting it to 0

StartClock ==
    /\  1aMsgs # {} \* at least one ballot must be started
    /\  clock' = 0
    /\  UNCHANGED <<maxBal, maxVBal, maxVVal, 1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs, rcvd1aMsgs, rcvd1bMsgs, rcvd2aMsgs, rcvd2bMsgs>>

IncrementClock ==
    /\ clock >= 0
    /\ clock < MaxTime
    /\ clock' = clock + 1
    \* after the clock is started, messages must be received in a timely manner:
    /\ \A a \in Acceptor :
        /\  \A m \in 1aMsgs : m[1] < clock => m \in rcvd1aMsgs[a]
    /\ \A m \in 1bMsgs : m[1] < clock => m \in rcvd1bMsgs
    \* nothing else changes except the clock:
    /\ UNCHANGED <<maxBal, maxVBal, maxVVal, 1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs, rcvd1aMsgs, rcvd1bMsgs, rcvd2aMsgs, rcvd2bMsgs>>

Phase1a(b) ==
    /\ clock = -1 \* once the clock is started, we are in a synchronous ballot that "lasts long enough"
    /\ 1aMsgs' = 1aMsgs \cup {<<clock,b>>}
    /\ UNCHANGED <<maxBal, maxVBal, maxVVal, 1bMsgs, 2aMsgs, 2bMsgs, rcvd1aMsgs, rcvd1bMsgs, rcvd2aMsgs, rcvd2bMsgs, clock>>

Receive1aMsg(a, m) ==
    /\  m \in 1aMsgs
    /\  rcvd1aMsgs' = [rcvd1aMsgs EXCEPT ![a] = @ \cup {m}]
    /\  LET b == m[2] IN
            IF b > maxBal[a]
            THEN \* Phase1b:
                /\ maxBal' = [maxBal EXCEPT ![a] = b]
                /\ 1bMsgs' = 1bMsgs \cup {<<clock, [acc |-> a, bal |-> b, mbal |-> maxVBal[a], mval |-> maxVVal[a]]>>}
                /\ UNCHANGED <<maxVBal, maxVVal, 1aMsgs, 2aMsgs, 2bMsgs, rcvd1bMsgs, rcvd2aMsgs, rcvd2bMsgs, clock>>
            ELSE UNCHANGED <<maxBal, maxVBal, maxVVal, 1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs, rcvd1bMsgs, rcvd2aMsgs, rcvd2bMsgs, clock>>

Receive1bMsg(m, v) ==
    /\  m \in 1bMsgs
    /\  rcvd1bMsgs' = rcvd1bMsgs \cup {m}
    /\  LET b == m[2].bal
        IN  IF  /\ \A m2a \in 2aMsgs : m2a.bal # b \* NOTE keep abstract
                /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v)
            THEN \* Phase2a:
                /\ 2aMsgs' = 2aMsgs \cup {[bal |-> b, val |-> v]}
                /\ UNCHANGED <<1aMsgs, 1bMsgs, maxBal, maxVBal, maxVVal, 2bMsgs, rcvd1aMsgs, rcvd2aMsgs, rcvd2bMsgs, clock>>
            ELSE 
                UNCHANGED <<maxBal, maxVBal, maxVVal, 1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs, rcvd1aMsgs, rcvd2aMsgs, rcvd2bMsgs, clock>>

Receive2aMsg(a, b, v) ==
    /\ [bal |-> b, val |-> v] \in 2aMsgs
    /\ rcvd2aMsgs' = [rcvd2aMsgs EXCEPT ![a] = @ \cup {[bal |-> b, val |-> v]}]
    /\ UNCHANGED <<maxBal, maxVBal, maxVVal, 1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs, rcvd1aMsgs, rcvd1bMsgs, rcvd2bMsgs, clock>>

Phase2b(a, b, v) ==
    /\ b \geq maxBal[a]
    /\ \E m \in rcvd2aMsgs[a] :
        /\ m.bal = b
        /\ maxBal' = [maxBal EXCEPT ![a] = b]
        /\ maxVBal' = [maxVBal EXCEPT ![a] = b]
        /\ maxVVal' = [maxVVal EXCEPT ![a] = m.val]
        /\ 2bMsgs' = 2bMsgs \cup {[acc |-> a, bal |-> b, val |-> m.val]}
    /\ UNCHANGED <<1aMsgs, 1bMsgs, 2aMsgs, rcvd1aMsgs, rcvd1bMsgs, rcvd2aMsgs, rcvd2bMsgs, clock>>

Receive2bMsg(a1, a2, b, v) ==
    /\ [acc |-> a2, bal |-> b, val |-> v] \in 2bMsgs
    /\ rcvd2bMsgs' = [rcvd2bMsgs EXCEPT ![a1] = @ \cup {[acc |-> a2, bal |-> b, val |-> v]}]
    /\ UNCHANGED <<maxBal, maxVBal, maxVVal, 1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs, rcvd1aMsgs, rcvd1bMsgs, rcvd2aMsgs, clock>>

Next == \E t \in Time : \E b \in Ballot, v \in Value, a \in Acceptor :
    \/ StartClock
    \/ IncrementClock
    \/ Phase1a(b)
    \/ Receive1aMsg(a, <<t, b>>)
    \/ \E mbal \in Ballot, mval \in Value : Receive1bMsg(<<t, [acc |-> a, bal |-> b, mbal |-> mbal, mval |-> mval]>>, v)
    \/ Receive2aMsg(a, b, v)
    \/ Phase2b(a, b, v)
    \/ \E a2 \in Acceptor : Receive2bMsg(a, a2, b, v)

Spec == Init /\ [][Next]_vars

TypeOK == /\ maxBal  \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVVal \in [Acceptor -> Value \cup {SomeValue}]
          /\ 1aMsgs \in SUBSET (Time\times Ballot)
          /\ 1bMsgs \in SUBSET (Time \times [acc : Acceptor, bal : Ballot, mbal : Ballot \cup {-1}, mval : Value])
          /\ 2aMsgs \in SUBSET [bal : Ballot, val : Value]
          /\ 2bMsgs \in SUBSET [acc : Acceptor, bal : Ballot, val : Value]
          /\ rcvd1aMsgs \in [Acceptor -> SUBSET (Time\times Ballot)]
          /\ rcvd1bMsgs \in SUBSET (Time\times [acc : Acceptor, bal : Ballot, mbal : Ballot \cup {-1}, mval : Value])
          /\ rcvd2aMsgs \in [Acceptor -> SUBSET [bal : Ballot, val : Value]]
          /\ rcvd2bMsgs \in [Acceptor -> SUBSET [acc : Acceptor, bal : Ballot, val : Value]]
          /\ clock \in {-1} \cup Time

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
    /\ \A t \in Time : <<t,b>> \in rcvd1aMsgs[a] => <<t,b>> \in 1aMsgs
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
        /\ m[2].mbal < m[2].bal
        /\ m[2].bal <= maxBal[m[2].acc]
        /\ m[2].mbal <= maxVBal[m[2].acc]
        /\ m[2].mbal = maxVBal[m[2].acc] => m[2].mval = maxVVal[m[2].acc]
        /\ m[2].mbal # -1 => [acc |-> m[2].acc, bal |-> m[2].mbal, val |-> m[2].mval] \in 2bMsgs
        /\ \A m2b \in 2bMsgs : m2b.acc = m[2].acc => 
              /\ \neg (m[2].mbal < m2b.bal /\ m2b.bal < m[2].bal)
              /\ m2b.bal = m[2].mbal => m2b.val = m[2].mval
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

Invariant_ == TypeOK /\ Invariant0 /\ Invariant1 /\ Invariant2
Invariant == Invariant0 /\ Invariant1 /\ Invariant2 /\ Correctness

======================================