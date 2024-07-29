------------ MODULE Paxos ------------

\* messages contain the time by which they must be received

EXTENDS Integers, FiniteSets, TLC

CONSTANT Value, Acceptor, Quorum, MaxBallot, MaxTime

Ballot ==  0..MaxBallot

Time == -1..MaxTime

SomeValue == CHOOSE v \in Value : TRUE

VARIABLES maxBal, maxVBal, maxVVal,
    1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs,
    rcvd1aMsgs, rcvd1bMsgs, rcvd2aMsgs,
    clock

vars == << maxBal, maxVBal, maxVVal, 1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs, rcvd1aMsgs, rcvd1bMsgs, rcvd2aMsgs, clock >>

ShowsSafeAt(M, Q, b, v) ==
    LET \* @type: Set(<<Int, {acc : ACCEPTOR, bal : Int, mbal : Int, mval : VALUE}>>);
        Q1b == {m \in M : m[2].bal = b /\ m[2].acc \in Q}
    IN  /\ \A a \in Q : \E m \in Q1b : m[2].acc = a
        /\  \/ \A m \in Q1b : m[2].mbal = -1
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
    \* /\ rcvd2bMsgs = [a \in Acceptor |-> {}]
    /\ clock = -1 \* the clock is started by setting it to 0

IncrementClock ==
    /\ clock < MaxTime
    /\ 1aMsgs # {}
    \* after the clock is started, messages must be received in a timely manner:
    /\ clock' = clock + 1
    /\ \A a \in Acceptor :
        /\ \A m \in 1aMsgs : m[1] < clock' => m \in rcvd1aMsgs[a]
        /\ \A m \in 2aMsgs : m[1] < clock' => m \in rcvd2aMsgs[a]
    /\ \A m \in 1bMsgs : m[1] < clock' => m \in rcvd1bMsgs
    \* nothing else changes except the clock:
    /\ UNCHANGED <<maxBal, maxVBal, maxVVal, 1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs, rcvd1aMsgs, rcvd1bMsgs, rcvd2aMsgs>>

Phase1a(b) ==
    /\ clock = -1 \* once the clock is started, we are in a synchronous ballot that "lasts long enough"
    /\ 1aMsgs' = 1aMsgs \cup {<<clock+1,b>>}
    /\ UNCHANGED <<maxBal, maxVBal, maxVVal, 1bMsgs, 2aMsgs, 2bMsgs, rcvd1aMsgs, rcvd1bMsgs, rcvd2aMsgs, clock>>

Receive1aMsg(a, m) ==
    /\  rcvd1aMsgs' = [rcvd1aMsgs EXCEPT ![a] = @ \cup {m}]
    /\  LET b == m[2] IN
            IF b > maxBal[a]
            THEN \* Phase1b:
                /\ maxBal' = [maxBal EXCEPT ![a] = b]
                /\ 1bMsgs' = 1bMsgs \cup {<<clock+1, [acc |-> a, bal |-> b, mbal |-> maxVBal[a], mval |-> maxVVal[a]]>>}
                /\ UNCHANGED <<maxVBal, maxVVal, 1aMsgs, 2aMsgs, 2bMsgs, rcvd1bMsgs, rcvd2aMsgs, clock>>
            ELSE UNCHANGED <<maxBal, maxVBal, maxVVal, 1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs, rcvd1bMsgs, rcvd2aMsgs, clock>>

(**********************************************************************************)
(* Here there was a mistake: v was a parameter quantified over in Next, and so by *)
(* picking the "wrong" v we could receive a quorum of 1b messages without sending *)
(* a 2a message. This was found only after 25 minutes of model-checking with 16   *)
(* cores and enough memory not to swap.                                           *)
(**********************************************************************************)
Receive1bMsg(m) ==
    /\  rcvd1bMsgs' = rcvd1bMsgs \cup {m}
    /\  LET b == m[2].bal
        IN  IF  /\ \A m2a \in 2aMsgs : m2a[2].bal # b \* NOTE keep abstract
                /\ \E Q \in Quorum, v \in Value : ShowsSafeAt(rcvd1bMsgs, Q, b, v)
            THEN \* Phase2a:
                /\ \E Q \in Quorum, v \in Value : 
                    /\ ShowsSafeAt(rcvd1bMsgs, Q, b, v) 
                    /\ 2aMsgs' = 2aMsgs \cup {<<clock+1, [bal |-> b, val |-> v]>>}
                /\ UNCHANGED <<1aMsgs, 1bMsgs, maxBal, maxVBal, maxVVal, 2bMsgs, rcvd1aMsgs, rcvd2aMsgs, clock>>
            ELSE 
                UNCHANGED <<maxBal, maxVBal, maxVVal, 1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs, rcvd1aMsgs, rcvd2aMsgs, clock>>

Receive2aMsg(a, m) ==
    /\  rcvd2aMsgs' = [rcvd2aMsgs EXCEPT ![a] = @ \cup {m}]
    /\  LET b == m[2].bal
            v == m[2].val
        IN  IF  b \geq maxBal[a]
            THEN
                /\ maxBal' = [maxBal EXCEPT ![a] = b]
                /\ maxVBal' = [maxVBal EXCEPT ![a] = b]
                /\ maxVVal' = [maxVVal EXCEPT ![a] = v]
                /\ 2bMsgs' = 2bMsgs \cup {[acc |-> a, bal |-> b, val |-> v]}
                /\ UNCHANGED <<1aMsgs, 1bMsgs, 2aMsgs, rcvd1aMsgs, rcvd1bMsgs, clock>>
            ELSE
                UNCHANGED <<maxBal, maxVBal, maxVVal, 1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs, rcvd1aMsgs, rcvd1bMsgs, clock>>

\* Receive2bMsg(a1, a2, b, v) ==
\*     /\ [acc |-> a2, bal |-> b, val |-> v] \in 2bMsgs
\*     /\ rcvd2bMsgs' = [rcvd2bMsgs EXCEPT ![a1] = @ \cup {[acc |-> a2, bal |-> b, val |-> v]}]
\*     /\ UNCHANGED <<maxBal, maxVBal, maxVVal, 1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs, rcvd1aMsgs, rcvd1bMsgs, rcvd2aMsgs, clock>>

Next ==
    \/  IncrementClock
    \/  \E b \in Ballot : Phase1a(b)
    \/  \E m \in 1bMsgs : Receive1bMsg(m)
    \/  \E a \in Acceptor :
            \/ \E m \in 1aMsgs : Receive1aMsg(a, m)
            \/ \E m \in 2aMsgs : Receive2aMsg(a, m)
    \* \/ \E a2 \in Acceptor : Receive2bMsg(a, a2, b, v)

Spec == Init /\ [][Next]_vars

TypeOK == /\ maxBal  \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVVal \in [Acceptor -> Value \cup {SomeValue}]
          /\ 1aMsgs \in SUBSET (Time\times Ballot)
          /\ 1bMsgs \in SUBSET (Time \times [acc : Acceptor, bal : Ballot, mbal : Ballot \cup {-1}, mval : Value])
          /\ 2aMsgs \in SUBSET (Time \times [bal : Ballot, val : Value])
          /\ 2bMsgs \in SUBSET [acc : Acceptor, bal : Ballot, val : Value]
          /\ rcvd1aMsgs \in [Acceptor -> SUBSET (Time\times Ballot)]
          /\ rcvd1bMsgs \in SUBSET (Time\times [acc : Acceptor, bal : Ballot, mbal : Ballot \cup {-1}, mval : Value])
          /\ rcvd2aMsgs \in [Acceptor -> SUBSET (Time \times [bal : Ballot, val : Value])]
        \*   /\ rcvd2bMsgs \in [Acceptor -> SUBSET [acc : Acceptor, bal : Ballot, val : Value]]
          /\ clock \in {-1} \cup Time

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

NoFutureVote == \A m \in 2bMsgs : m.bal <= maxVBal[m.acc]
OneVotePerBallot == \A m1,m2 \in 2aMsgs : m1[2].bal = m2[2].bal => m1 = m2
OneValuePerBallot == \A m1,m2 \in 2bMsgs : m1.bal = m2.bal => m1.val = m2.val
VoteForProposal == \A m1 \in 2bMsgs : \E m2 \in 2aMsgs : m1.bal = m2[2].bal /\ m1.val = m2[2].val

TypeOK_ == TypeOK

Invariant0 == \A a \in Acceptor : \A b \in Ballot :
    /\ \A m \in rcvd1aMsgs[a] : m \in 1aMsgs
    /\ \A m \in rcvd2aMsgs[a] : m \in 2aMsgs
    \* /\ \A m \in rcvd2bMsgs[a] : m \in 2bMsgs
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
    SafeAt(m[2].val, m[2].bal)
Invariant2_ == TypeOK /\ Invariant0 /\ Invariant1 /\ Invariant2    

Correctness_ == TypeOK /\ Invariant0 /\ Invariant1 /\ Invariant2

Invariant_ == TypeOK /\ Invariant0 /\ Invariant1 /\ Invariant2
Invariant == Invariant0 /\ Invariant1 /\ Invariant2 /\ Correctness

\* Now the liveness property:

Liveness ==
    clock > 2 => \E b \in Ballot, v \in Value : Chosen(v)

Max(S) == CHOOSE x \in S : \A y \in S : x >= y

LivenessInvariant0 ==
    /\  \A m \in 1aMsgs :
        /\  m[1] = 0
        /\  m[1] < clock => \A a \in Acceptor : m \in rcvd1aMsgs[a]
    /\  \A m \in 1bMsgs :
        /\  0 <= m[1]
        /\  m[1] <= 1
        /\  m[1] <= clock+1
        /\  m[1] < clock => m \in rcvd1bMsgs
    /\  \A m \in 2aMsgs :
        /\  0 <= m[1]
        /\  m[1] <= clock+1
        /\  m[1] < clock => \A a \in Acceptor : m \in rcvd2aMsgs[a]
    /\  \A 2aMsg \in 2aMsgs : \E Q \in Quorum : \A a \in Q : \E 1bMsg \in rcvd1bMsgs :
            /\  1bMsg[2].bal = 2aMsg[2].bal
            /\  1bMsg[2].acc = a
    /\  \A 1bMsg \in 1bMsgs : \E 1aMsg \in rcvd1aMsgs[1bMsg[2].acc] : 1aMsg[2] = 1bMsg[2].bal
    /\  \A a \in Acceptor : maxBal[a] > -1 => \E m \in 1aMsgs : maxBal[a] = m[2]
LivenessInvariant0_ == TypeOK /\ LivenessInvariant0 /\ Invariant0 /\ Invariant1

LivenessInvariant1 == LET mb == Max({1aMsg[2] : 1aMsg \in 1aMsgs}) IN
    clock > 0 =>
        /\  \A a \in Acceptor, m \in 1aMsgs : m \in rcvd1aMsgs[a]
        /\  \E Q \in Quorum : \A a \in Q : \E m \in 1bMsgs :
                /\  m[2].acc = a 
                /\  m[2].bal = mb
                /\  m[1] < 2
LivenessInvariant1_ == TypeOK /\ LivenessInvariant0 /\ Invariant0 /\ Invariant1 /\ LivenessInvariant1

LivenessInvariant2 == LET mb == Max({1aMsg[2] : 1aMsg \in 1aMsgs}) IN
    clock > 1 =>
        /\  \A m \in 1bMsgs : m[1] <= 1
        \* /\  \E m \in 2aMsgs : m[2].bal = mb
LivenessInvariant2_ == TypeOK /\ LivenessInvariant0 /\ Invariant0 /\ Invariant1 /\ LivenessInvariant1 /\ LivenessInvariant2


======================================