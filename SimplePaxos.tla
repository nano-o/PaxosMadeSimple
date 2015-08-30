-------------------------------- MODULE SimplePaxos -------------------------

(***************************************************************************)
(* A formalization of the algorithm described in the paper "Paxos Made     *)
(* Simple", by Leslie Lamport.                                             *)
(*                                                                         *)
(* We specify how commands get chosen but not how learners learn a chosen  *)
(* value.                                                                  *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets

(***************************************************************************)
(* We consider a set of processes P, each of which plays both the roles of *)
(* proposer and acceptor (we do not specify learners and how they may      *)
(* learn chosen values).                                                   *)
(***************************************************************************)
CONSTANTS 
    P, \* The set of processes. 
    C \* The set of commands.

(***************************************************************************)
(* The variables of the spec.  See TypeInvariant for the expected values   *)
(* of those variables and comments.                                        *)
(***************************************************************************)
VARIABLES
    proposalNumber,
    numbersUsed,
    proposed,
    accepted,
    lastPromise,
    network

vars == <<proposalNumber, proposed, accepted, 
    lastPromise, network>>
    
(***************************************************************************)
(* We assume that proposal numbers start at 1 and we will use 0 to         *)
(* indicate special conditions.                                            *)
(***************************************************************************)
ProposalNum == Nat \ {0}

Proposal == [command : C, number: ProposalNum]

Msg(type, Payload) == [type : {type}, payload : Payload]

(***************************************************************************)
(* Msgs is the set of messages that process can send.  We do not model     *)
(* explicitely the source and destination of messages and assume that      *)
(* every process sees the entire state of the network.  For example, a     *)
(* process will know that a prepare-reponse message is a response to its   *)
(* prepare message by looking at the propoal number in the messages.       *)
(***************************************************************************)
Msgs == 
    [   type : {"prepare"}, 
        number : ProposalNum ] 
    \cup
    [   type : {"prepare-response"}, 
        highestAccepted: Proposal \cup {<<>>}, \* we use <<>> to indicate that no proposal was ever accepted. 
        number: ProposalNum, 
        from: P ] 
    \cup
    [   type: {"propose"},
        proposal : Proposal ]

TypeInvariant ==
    \A p \in P :
        /\  proposalNumber[p] \in ProposalNum \cup {0} \* The current proposal number of process p.
        /\  proposed[p] \in BOOLEAN \* Did p make a proposal for its current proposal number?
        /\  numbersUsed[p] \in SUBSET ProposalNum \* All the proposal numbers ever used by p up to this point.
        /\  accepted[p] \in Proposal  \cup {<<>>} \* The last proposal that p has accepted.
        /\  lastPromise[p] \in ProposalNum \cup {0} \* The last promise made by p.
        /\  network \in SUBSET Msgs \* A set of messages.

Init == 
    /\  proposalNumber = [p \in P |-> 0]
    /\  proposed = [p \in P |-> FALSE]
    /\  numbersUsed = [p \in P |-> {}]
    /\  accepted = [p \in P |-> <<>>]
    /\  lastPromise = [p \in P |-> 0]
    /\  network = {}
    
(***************************************************************************)
(* The proposer p starts the prepare phase by chosing a new proposal       *)
(* number and asking all the acceptors not to accept proposals with a      *)
(* lower number and to report the highest proposal that they have          *)
(* accepted.                                                               *)
(*                                                                         *)
(* We require that two different proposers never use the same proposal     *)
(* numbers.                                                                *)
(*                                                                         *)
(* Note that a proposer can start a new prepare phase with a greater       *)
(* proposal number at any time.                                            *)
(***************************************************************************)
Prepare(p) == \E n \in ProposalNum :
    /\  n > proposalNumber[p]
    /\  \A q \in P : n \notin numbersUsed[q]
    /\  proposalNumber' = [proposalNumber EXCEPT ![p] = n]
    /\  proposed' = [proposed EXCEPT ![p] = FALSE]
    /\  network' = network \cup {[type |-> "prepare", number |-> n]}
    /\  numbersUsed' = [numbersUsed EXCEPT ![p] = @ \cup {n}]
    /\  UNCHANGED <<accepted, lastPromise>>

PrepareReponse(p) == 
    /\  \E m \in network :
            /\  m.type = "prepare"
            /\  m.number > lastPromise[p]
            /\  lastPromise' = [lastPromise EXCEPT ![p] = m.number]
            /\  network' = network \cup {[
                    type |-> "prepare-response",
                    from |-> p, 
                    highestAccepted |-> accepted[p], 
                    number |-> m.number ]}
    /\  UNCHANGED <<proposalNumber, accepted, proposed, numbersUsed>>

MajoritySets == {Q \in SUBSET P : Cardinality(Q) > Cardinality(P) \div 2}

HighestProposal(proposals) == 
    CHOOSE p \in proposals :
        /\  \A q \in proposals : p # q => p.number > q.number

IsPrepareResponse(p, m) ==
    /\  m.type = "prepare-response"
    /\  m.number = proposalNumber[p]

SendProposal(p, c) ==
    network' = network \cup {[
        type |-> "propose",
        proposal |-> [
            command |-> c,
            number |-> proposalNumber[p] ]]}

(***************************************************************************)
(* The set of highest accepted proposals found in the prepare-response     *)
(* messages sent by the members of Q in response to the last prepare       *)
(* message of process p.                                                   *)
(***************************************************************************)
HighestAccepted(p, Q) ==
    {m.highestAccepted : m \in {m \in network :
        /\  IsPrepareResponse(p,m)
        /\  m.from \in Q
        /\  m.highestAccepted # <<>>}}

(***************************************************************************)
(* A proposer can propose a command if it has not already done so for its  *)
(* current proposal number and if it has received reponses to its prepare  *)
(* message from a majority of acceptors.                                   *)
(***************************************************************************)
Propose(p) == 
    /\  proposed[p] = FALSE \* Don't let p propose different values with the same proposal number.
    /\  \E Q \in MajoritySets :   
            /\  \A q \in Q : \E m \in network :
                    /\  IsPrepareResponse(p,m)
                    /\  m.from = q
            /\  LET proposals == HighestAccepted(p, Q)
                IN  IF  proposals # {}
                    THEN    LET c == HighestProposal(proposals).command
                            IN  /\  SendProposal(p, c)
                                /\  proposed' = 
                                        [proposed EXCEPT ![p] = TRUE]
                    ELSE
                        \E c \in C :
                            /\  SendProposal(p, c)
                            /\  proposed' = 
                                        [proposed EXCEPT ![p] = TRUE]
    /\  UNCHANGED <<proposalNumber, accepted, lastPromise, numbersUsed>> 
             
(***************************************************************************)
(* An acceptor accepts a proposal.  In the paper, it is not said that,     *)
(* after accepting a command, p should not accept new commands that have a *)
(* lower number.  However this leads to a bug, which can be found by TLC   *)
(* by remove the line as instructed below.  This bug is discussed on       *)
(* stackoverflow:                                                          *)
(* `^\url{http://stackoverflow.com/questions/29880949/contradiction-in-lamports-paxos-made-simple-paper}^' *)
(***************************************************************************)   
Accept(p) ==
    /\  \E m \in network :
            /\  m.type = "propose"
            /\  m.proposal.number \geq lastPromise[p]
            \* One way to fix the "bug" reported on stackoverflow (remove this line to reproduce the bug):
            /\  lastPromise' = [lastPromise EXCEPT ![p] = m.proposal.number]
            /\  accepted' = [accepted EXCEPT ![p] = m.proposal]
    /\  UNCHANGED  <<network, proposalNumber, proposed, numbersUsed>>

Next == \E p \in P :
    \/  Prepare(p)
    \/  PrepareReponse(p)
    \/  Propose(p)
    \/  Accept(p)

        
IsChosen(c, acc) ==
    \E Q \in MajoritySets : \A q \in Q :
        /\  acc[q] # <<>>
        /\  acc[q].command = c

(***************************************************************************)
(* Agreement says that if a command is chosen, then no different command   *)
(* can be chosen at a later time.                                          *)
(*                                                                         *)
(* One might be tempted to add the fact that IsChosen(c, accepted) must be *)
(* stable, like below.  However the algorithm violates this property.      *)
(* This is however not a problem: it may prevent learners to learn about a *)
(* chosen value without triggering a new proposal.  In practice the same   *)
(* problem happens with crashes (which are not modeled here), and Lamport  *)
(* addresses it in section 2.3.                                            *)
(*                                                                         *)
(* WrongAgreement ==                                                       *)
(*     \A c \in C : [](IsChosen(c, accepted) =>                            *)
(*         /\  (\A d \in C : d # c => [](\neg IsChosen(d, accepted)))      *)
(*         /\  []IsChosen(c, accepted))                                    *)
(***************************************************************************)
Agreement == 
    \A c \in C : [](IsChosen(c, accepted) => 
        (\A d \in C : d # c => [](\neg IsChosen(d, accepted))))
        
=============================================================================
\* Modification History
\* Last modified Sun Aug 30 15:21:48 EDT 2015 by nano
\* Created Sat Aug 29 17:37:33 EDT 2015 by nano
