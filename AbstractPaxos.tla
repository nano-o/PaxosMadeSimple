------------------------------- MODULE AbstractPaxos -------------------------------

(********************************************************************************)
(* Now let's tackle liveness. We will non-deterministically, irrevocably block  *)
(* starting new ballots in order to model a ballot lasting long enough. Then we *)
(* will show that, when no transitions are enabled anymore, we have a chosen    *)
(* value.                                                                       *)
(********************************************************************************)

EXTENDS Integers

CONSTANTS
    Value,
    Acceptor,
    Quorum,
    Ballot

VARIABLES
    votes,
    maxBal,
    crashed,
    goodBallot

TypeOK ==
    /\ votes \in [Acceptor -> SUBSET (Ballot\times Value)]
    /\ maxBal \in [Acceptor -> Ballot\cup {-1}]
    /\ crashed \in SUBSET Acceptor
    /\ goodBallot \in BOOLEAN

VotedFor(a, b, v) == <<b, v>> \in votes[a]

ChosenAt(b, v) ==
  \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

DidNotVoteAt(a, b) == \A v \in Value : ~ VotedFor(a, b, v)

CannotVoteAt(a, b) == /\ maxBal[a] > b
                      /\ DidNotVoteAt(a, b)
NoneOtherChoosableAt(b, v) ==
   \E Q \in Quorum :
     \A a \in Q : VotedFor(a, b, v) \/ CannotVoteAt(a, b)

SafeAt(b, v) == \A c \in Ballot : c < b => NoneOtherChoosableAt(c, v)

ShowsSafeAt(Q, b, v) ==
  /\ \A a \in Q : maxBal[a] \geq b
  \* NOTE: `^Apalache^' does not support non-constant integer ranges (e.g. we cannot write (c+1)..(b-1))
  /\ \E c \in Ballot\cup {-1} :
    /\ c < b
    /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
    /\ \A d \in Ballot : c < d /\ d < b => \A a \in Q : DidNotVoteAt(a, d)

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ maxBal = [a \in Acceptor |-> -1]
    /\ crashed = {}
    /\ goodBallot = FALSE

Crash(a) ==
    /\  crashed' = crashed \cup {a}
    /\  \E Q \in Quorum : \A a2 \in Q : a2 \notin crashed'
    /\  UNCHANGED <<votes, maxBal, goodBallot>>

IncreaseMaxBal(a, b) ==
  /\ a \notin crashed
  \* once a good ballot started, we cannot increase maxBal beyond it:
  /\ goodBallot => \E a2 \in Acceptor : b <= maxBal[a2]
  /\ b > maxBal[a]
  /\ maxBal' = [maxBal EXCEPT ![a] = b]
  /\ UNCHANGED <<votes, crashed, goodBallot>>

IncreaseMaxBal_ENABLED(a, b) ==
  /\ a \notin crashed
  /\ goodBallot => \E a2 \in Acceptor : b <= maxBal[a2]
  /\ b > maxBal[a]

VoteFor(a, b, v) ==
    /\ a \notin crashed
    /\ maxBal[a] \leq b
    /\ \A vt \in votes[a] : vt[1] # b
    /\ \A c \in Acceptor \ {a} :
         \A vt \in votes[c] : (vt[1] = b) => (vt[2] = v)
    /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v)
    /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ UNCHANGED <<crashed, goodBallot>>

VoteFor_ENABLED(a, b, v) ==
    /\ a \notin crashed
    /\ maxBal[a] \leq b
    /\ \A vt \in votes[a] : vt[1] # b
    /\ \A c \in Acceptor \ {a} :
         \A vt \in votes[c] : (vt[1] = b) => (vt[2] = v)
    /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v)

StartGoodBallot ==
    /\ \E a \in Acceptor : maxBal[a] > -1
    /\ goodBallot' = TRUE
    /\ UNCHANGED <<votes, maxBal, crashed>>

Next  ==  \E a \in Acceptor, b \in Ballot :
            \/ IncreaseMaxBal(a, b)
            \/ \E v \in Value : VoteFor(a, b, v)
            \/ Crash(a)
            \/ StartGoodBallot

Spec == Init /\ [][Next]_<<votes, maxBal, crashed, goodBallot>>

VotesSafe == \A a \in Acceptor, b \in Ballot, v \in Value :
                 VotedFor(a, b, v) => SafeAt(b, v)

OneValuePerBallot ==
    \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value :
       VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)

NoVoteAfterMaxBal == \A a \in Acceptor, b \in Ballot, v \in Value :
    <<b,v>> \in votes[a] => /\ b <= maxBal[a]

Consistency == \A v,w \in chosen : v = w

\* This invariant is inductive and establishes consistency:
Invariant ==
  /\ TypeOK
  /\ VotesSafe
  /\ OneValuePerBallot
  /\ NoVoteAfterMaxBal
  /\ Consistency
Invariant_ == Invariant

\* TLC can handle ENABLED, but not Apalache
Liveness ==
    /\ goodBallot
    /\ \A a \in Acceptor, b \in Ballot, v \in Value :
        /\ \neg IncreaseMaxBal_ENABLED(a, b)
        /\ \neg VoteFor_ENABLED(a, b, v)
        \* /\ \neg ENABLED IncreaseMaxBal(a, b)
        \* /\ \neg ENABLED VoteFor(a, b, v)
    => chosen # {}

\* NOTE: CHOOSE is dangerous! I had forgotten -1 and was getting weird results.
maxBallot == CHOOSE b \in Ballot \cup {-1}:
    /\  \A a \in Acceptor : maxBal[a] <= b
    /\  \E a \in Acceptor : maxBal[a] = b

\* Supporting invariant for liveness:
LivenessInvariant == 
    /\  TypeOK
    /\  OneValuePerBallot
    /\  \E Q \in Quorum : Q \cap crashed = {}
    /\  \A a \in Acceptor, b \in Ballot, v \in Value : <<b,v>> \in votes[a] => 
            \E Q \in Quorum : ShowsSafeAt(Q, b, v)
    /\  goodBallot =>
        /\  maxBallot > -1
        /\  \A a \in Acceptor :
            /\  (\A b \in Ballot : \neg IncreaseMaxBal_ENABLED(a, b)) =>
                    \/  a \in crashed 
                    \/  maxBal[a] = maxBallot
            /\  \A b \in Ballot :
                    (maxBal[a] <= b /\ (\A v \in Value : \neg VoteFor_ENABLED(a, b, v))) =>
                        \/  a \in crashed
                        \/  \E v2 \in Value : <<b,v2>> \in votes[a]
                        \/  \A Q \in Quorum : \E a2 \in Q : maxBal[a2] < b
LivenessInvariant_ == LivenessInvariant

Liveness_ ==
    LivenessInvariant
    
Canary1 == \neg (
    \A a \in Acceptor, b \in Ballot, v \in Value :
        /\ \neg IncreaseMaxBal_ENABLED(a, b)
        /\ \neg VoteFor_ENABLED(a, b, v)
)

=====================================================================================