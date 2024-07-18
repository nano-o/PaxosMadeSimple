-------------------------- MODULE PaxosMadeSimple --------------------------

(*************************************************************************)
(* A specification of the algorithm described in Paxos Made Simple. This *)
(* specification is a modification of:                                   *)
(* `^\url{https://lamport.azurewebsites.net/tla/PConProof.tla^'          *)
(* Look there for comments.                                              *)
(*************************************************************************)

EXTENDS Integers, FiniteSets, TLC

CONSTANT Value, Acceptor, Quorum

ASSUME QA == /\ \A Q \in Quorum : Q \subseteq Acceptor 
             /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 

Ballot ==  Nat

ASSUME BallotAssump == (Ballot \cup {-1}) \cap Acceptor = {}

None == CHOOSE v : v \notin Value
 
Message ==      [type : {"1a"}, bal : Ballot]
           \cup [type : {"1b"}, acc : Acceptor, bal : Ballot,
                 mbal : Ballot \cup {-1}, mval : Value \cup {None}]
           \cup [type : {"2a"}, bal : Ballot, val : Value]
           \cup [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]

(*--algorithm PCon {
  variables maxBal  = [a \in Acceptor |-> -1] ,
            maxVBal = [a \in Acceptor |-> -1] ,
            maxVVal = [a \in Acceptor |-> None] ,
            msgs = {}
  define {
    sentMsgs(t, b) == {m \in msgs : (m.type = t) /\ (m.bal = b)}
    
    ShowsSafeAt(Q, b, v) ==
      LET Q1b == {m \in sentMsgs("1b", b) : m.acc \in Q}
      IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a 
          /\ \/ \A m \in Q1b : m.mbal = -1
             \/ \E m \in Q1b :
                /\ m.mval = v
                /\ \A m1 \in Q1b : m1.mbal <= m.mbal
    }
 
  macro Phase1a() { msgs := msgs \cup {[type |-> "1a", bal |-> self]} ; }
  
  macro Phase1b(b) {
    when (b > maxBal[self]) /\ (sentMsgs("1a", b) # {});
    maxBal[self] := b;
    msgs := msgs \cup {[type |-> "1b", acc |-> self, bal |-> b, 
                        mbal |-> maxVBal[self], mval |-> maxVVal[self]]} ;
   }

  macro Phase2a(v) {
    when /\ sentMsgs("2a", self) = {}
         /\ \E Q \in Quorum : ShowsSafeAt(Q, self, v);
    msgs := msgs \cup {[type |-> "2a", bal |-> self, val |-> v]};
   }

  macro Phase2b(b) {
    when b \geq maxBal[self];
    with (m \in sentMsgs("2a", b)) {
        maxBal[self] := b;
        maxVBal[self] := b;
        maxVVal[self] := m.val;
        msgs := msgs \cup {[type |-> "2b", acc |-> self, bal |-> b, val |-> m.val]}
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
\* BEGIN TRANSLATION (chksum(pcal) = "c48275ec" /\ chksum(tla) = "72a9972f")
VARIABLES maxBal, maxVBal, maxVVal, msgs

(* define statement *)
sentMsgs(t, b) == {m \in msgs : (m.type = t) /\ (m.bal = b)}

ShowsSafeAt(Q, b, v) ==
  LET Q1b == {m \in sentMsgs("1b", b) : m.acc \in Q}
  IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
      /\ \/ \A m \in Q1b : m.mbal = -1
         \/ \E m \in Q1b :
            /\ m.mval = v
            /\ \A m1 \in Q1b : m1.mbal <= m.mbal


vars == << maxBal, maxVBal, maxVVal, msgs >>

ProcSet == (Acceptor) \cup (Ballot)

Init == (* Global variables *)
        /\ maxBal = [a \in Acceptor |-> -1]
        /\ maxVBal = [a \in Acceptor |-> -1]
        /\ maxVVal = [a \in Acceptor |-> None]
        /\ msgs = {}

acceptor(self) == \E b \in Ballot:
                    \/ /\ (b > maxBal[self]) /\ (sentMsgs("1a", b) # {})
                       /\ maxBal' = [maxBal EXCEPT ![self] = b]
                       /\ msgs' = (msgs \cup {[type |-> "1b", acc |-> self, bal |-> b,
                                               mbal |-> maxVBal[self], mval |-> maxVVal[self]]})
                       /\ UNCHANGED <<maxVBal, maxVVal>>
                    \/ /\ b \geq maxBal[self]
                       /\ \E m \in sentMsgs("2a", b):
                            /\ maxBal' = [maxBal EXCEPT ![self] = b]
                            /\ maxVBal' = [maxVBal EXCEPT ![self] = b]
                            /\ maxVVal' = [maxVVal EXCEPT ![self] = m.val]
                            /\ msgs' = (msgs \cup {[type |-> "2b", acc |-> self, bal |-> b, val |-> m.val]})

leader(self) == /\ \/ /\ msgs' = (msgs \cup {[type |-> "1a", bal |-> self]})
                   \/ /\ \E v \in Value:
                           /\ /\ sentMsgs("2a", self) = {}
                              /\ \E Q \in Quorum : ShowsSafeAt(Q, self, v)
                           /\ msgs' = (msgs \cup {[type |-> "2a", bal |-> self, val |-> v]})
                /\ UNCHANGED << maxBal, maxVBal, maxVVal >>

Next == (\E self \in Acceptor: acceptor(self))
           \/ (\E self \in Ballot: leader(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

TypeOK == /\ maxBal  \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVVal \in [Acceptor -> Value \cup {None}]
          /\ msgs \subseteq Message    

ChosenIn(b, v) ==
    \E Q \in Quorum : \A a \in Q : 
        \E m \in sentMsgs("2b", b) : 
            /\  m.acc = a
            /\  m.val = v
                      
Chosen(v) == \E b \in Ballot : ChosenIn(b,v)

Correctness ==
    \A v1,v2 \in Value : Chosen(v1) /\ Chosen(v2) => v1 = v2

THEOREM Spec => []Correctness

=============================================================================
\* Modification History
\* Last modified Thu Jul 18 15:30:44 PDT 2024 by nano
\* Created Thu Sep 03 22:58:03 EDT 2015 by nano
