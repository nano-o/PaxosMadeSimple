------------ MODULE Paxos ------------

EXTENDS Integers, FiniteSets, TLC

CONSTANT Value, Acceptor, Quorum

Ballot ==  Nat

SomeValue == CHOOSE v \in Value : TRUE

(*--algorithm PCon {
  variables maxBal  = [a \in Acceptor |-> -1],
            maxVBal = [a \in Acceptor |-> -1],
            maxVVal = [a \in Acceptor |-> SomeValue],
            1aMsgs = {},
            1bMsgs = {},
            2aMsgs = {},
            2bMsgs = {},
  define {
    
    ShowsSafeAt(Q, b, v) ==
      LET Q1b == {m \in 1bMsgs : m.bal = b /\ m.acc \in Q}
      IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
          /\ \/ \A m \in Q1b : m.mbal = -1
             \/ \E m \in Q1b :
                /\ m.mval = v
                /\ \A m1 \in Q1b : m1.mbal <= m.mbal
    }
 
  macro Phase1a() { 1aMsgs := 1aMsgs \cup {self} ; }
  
  macro Phase1b(b) {
    when b > maxBal[self] /\ b \in 1aMsgs;
    maxBal[self] := b;
    1bMsgs := 1bMsgs \cup {[acc |-> self, bal |-> b, mbal |-> maxVBal[self], mval |-> maxVVal[self]]};
   }

  macro Phase2a(v) {
    when /\ \A m \in 2aMsgs : m.bal # self
         /\ \E Q \in Quorum : ShowsSafeAt(Q, self, v);
    2aMsgs := 2aMsgs \cup {[bal |-> self, val |-> v]};
   }

  macro Phase2b(b) {
    when b \geq maxBal[self];
    with (m \in {m \in 2aMsgs : m.bal = b}) {
        maxBal[self] := b;
        maxVBal[self] := b;
        maxVVal[self] := m.val;
        2bMsgs := 2bMsgs \cup {[acc |-> self, bal |-> b, val |-> m.val]}
    }
   }
   
  process (acceptor \in Acceptor) {
    acc: while (TRUE) { 
            with (b \in Ballot) { either Phase1b(b) or Phase2b(b)  } }
   }

  process (leader \in Ballot) {
    ldr: while (TRUE) {
          either Phase1a()
          or     with (v \in Value) { Phase2a(v) }
         }
   }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "83a5f188" /\ chksum(tla) = "88f65c6f")
VARIABLES maxBal, maxVBal, maxVVal, 1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs

(* define statement *)
ShowsSafeAt(Q, b, v) ==
  LET Q1b == {m \in 1bMsgs : m.bal = b /\ m.acc \in Q}
  IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
      /\ \/ \A m \in Q1b : m.mbal = -1
         \/ \E m \in Q1b :
            /\ m.mval = v
            /\ \A m1 \in Q1b : m1.mbal <= m.mbal


vars == << maxBal, maxVBal, maxVVal, 1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs >>

ProcSet == (Acceptor) \cup (Ballot)

Init == (* Global variables *)
        /\ maxBal = [a \in Acceptor |-> -1]
        /\ maxVBal = [a \in Acceptor |-> -1]
        /\ maxVVal = [a \in Acceptor |-> SomeValue]
        /\ 1aMsgs = {}
        /\ 1bMsgs = {}
        /\ 2aMsgs = {}
        /\ 2bMsgs = {}

acceptor(self) == /\ \E b \in Ballot:
                       \/ /\ b > maxBal[self] /\ b \in 1aMsgs
                          /\ maxBal' = [maxBal EXCEPT ![self] = b]
                          /\ 1bMsgs' = (1bMsgs \cup {[acc |-> self, bal |-> b, mbal |-> maxVBal[self], mval |-> maxVVal[self]]})
                          /\ UNCHANGED <<maxVBal, maxVVal, 2bMsgs>>
                       \/ /\ b \geq maxBal[self]
                          /\ \E m \in {m \in 2aMsgs : m.bal = b}:
                               /\ maxBal' = [maxBal EXCEPT ![self] = b]
                               /\ maxVBal' = [maxVBal EXCEPT ![self] = b]
                               /\ maxVVal' = [maxVVal EXCEPT ![self] = m.val]
                               /\ 2bMsgs' = (2bMsgs \cup {[acc |-> self, bal |-> b, val |-> m.val]})
                          /\ UNCHANGED 1bMsgs
                  /\ UNCHANGED << 1aMsgs, 2aMsgs >>

leader(self) == /\ \/ /\ 1aMsgs' = (1aMsgs \cup {self})
                      /\ UNCHANGED 2aMsgs
                   \/ /\ \E v \in Value:
                           /\ /\ \A m \in 2aMsgs : m.bal # self
                              /\ \E Q \in Quorum : ShowsSafeAt(Q, self, v)
                           /\ 2aMsgs' = (2aMsgs \cup {[bal |-> self, val |-> v]})
                      /\ UNCHANGED 1aMsgs
                /\ UNCHANGED << maxBal, maxVBal, maxVVal, 1bMsgs, 2bMsgs >>

Next == (\E self \in Acceptor: acceptor(self))
           \/ (\E self \in Ballot: leader(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

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
