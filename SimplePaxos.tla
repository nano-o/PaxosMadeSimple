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

VARIABLES
    proposalNumber,
    numbersUsed,
    proposed,
    accepted,
    lastPromise,
    network,
    chosen

vars == <<proposalNumber, proposed, accepted, 
    lastPromise, network, chosen>>
    
(***************************************************************************)
(* We assume that proposal numbers start at 1 and we will use 0 to         *)
(* indicate special conditions.                                            *)
(***************************************************************************)
ProposalNum == Nat \ {0}

Proposal == [command : C, number: ProposalNum]

Msg(type, Payload) == [type : {type}, payload : Payload]

Msgs == 
    [   type : {"prepare"}, 
        number : ProposalNum ] 
    \cup
    [   type : {"prepare-response"}, 
        proposal: Proposal \cup {<<>>}, 
        number: ProposalNum, 
        from: P ] 
    \cup
    [   type: {"propose"},
        proposal : Proposal ]

TypeInvariant ==
    \A p \in P :
        /\  proposalNumber[p] \in ProposalNum \cup {0}
        /\  proposed[p] \in BOOLEAN \* Did p make a proposal for its current proposal number?
        /\  numbersUsed[p] \in SUBSET ProposalNum
        /\  accepted[p] \in Proposal  \cup {<<>>}
        /\  lastPromise[p] \in ProposalNum \cup {0}
        /\  network \in SUBSET Msgs
        /\  chosen \in SUBSET C \* A ghost variable used for debugging.

Init == 
    /\  proposalNumber = [p \in P |-> 0]
    /\  proposed = [p \in P |-> FALSE]
    /\  numbersUsed = [p \in P |-> {}]
    /\  accepted = [p \in P |-> <<>>]
    /\  lastPromise = [p \in P |-> 0]
    /\  network = {}
    /\  chosen = {}
    
(***************************************************************************)
(* The proposer p starts the prepare phase by chosing a new proposal       *)
(* number and asking all the acceptors not to accept proposals with a      *)
(* lower number and to report the highest proposal that they have          *)
(* accepted.                                                               *)
(*                                                                         *)
(* We assume that two different proposers never use the same proposal      *)
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
    /\  UNCHANGED <<accepted, lastPromise, chosen>>

PrepareReponse(p) == 
    /\  \E m \in network :
            /\  m.type = "prepare"
            /\  m.number > lastPromise[p]
            /\  lastPromise' = [lastPromise EXCEPT ![p] = m.number]
            /\  network' = network \cup {[
                    type |-> "prepare-response",
                    from |-> p, 
                    proposal |-> accepted[p], 
                    number |-> m.number ]}
    /\  UNCHANGED <<proposalNumber, accepted, proposed, chosen, numbersUsed>>

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

ProposalsInPrepareResponses(p, Q) ==
    {m.proposal : m \in {m \in network :
        /\  IsPrepareResponse(p,m)
        /\  m.from \in Q
        /\  m.proposal # <<>>}}

Propose(p) == 
    /\  proposed[p] = FALSE \* Don't let p propose different values with the same proposal number.
    /\  \E Q \in MajoritySets :   
            /\  \A q \in Q : \E m \in network :
                    /\  IsPrepareResponse(p,m)
                    /\  m.from = q
            /\  LET proposals == ProposalsInPrepareResponses(p, Q)
                IN  IF  proposals # {}
                    THEN    LET c == HighestProposal(proposals).command
                            IN  /\  SendProposal(p, c)
                                /\  proposed' = 
                                        [proposed EXCEPT ![p] = TRUE]
                    ELSE
                        \E c \in C : 
                            \* Anothe way to fix the "bug" reported on stackoverflow:
                            \* Send the proposal only to Q
                            /\  SendProposal(p, c)
                            /\  proposed' = 
                                        [proposed EXCEPT ![p] = TRUE]
    /\  UNCHANGED <<proposalNumber, accepted, lastPromise, chosen, numbersUsed>> 
        
IsChosen(c, acc) ==
    \E Q \in MajoritySets : \A q \in Q :
        /\  acc[q] # <<>>
        /\  acc[q].command = c
                
Accept(p) ==
    /\  \E m \in network :
            /\  m.type = "propose"
            /\  m.proposal.number \geq lastPromise[p]
            \* One way to fix the "bug" reported on stackoverflow:
            /\  lastPromise' = [lastPromise EXCEPT ![p] = m.proposal.number]
            /\  accepted' = [accepted EXCEPT ![p] = m.proposal]
            /\  IF  IsChosen(m.proposal.command, accepted')
                THEN chosen' = chosen \cup {m.proposal.command}
                ELSE UNCHANGED chosen
    /\  UNCHANGED  <<network, proposalNumber, proposed, numbersUsed>>

Next == \E p \in P :
    \/  Prepare(p)
    \/  PrepareReponse(p)
    \/  Propose(p)
    \/  Accept(p)

(***************************************************************************)
(* Agreement says that if a command is chosen, then no different command   *)
(* can be chosen at a later time.                                          *)
(*                                                                         *)
(* On might be tempted to add the fact that IsChosen(c, accepted) must be  *)
(* stable, like this:                                                      *)
(*                                                                         *)
(* Agreement ==                                                            *)
(*     \A c \in C : [](IsChosen(c, accepted) =>                            *)
(*         /\  (\A d \in C : d # c => [](\neg IsChosen(d, accepted))))     *)
(*         /\  [](IsChosen(c, accepted)                                    *)
(*                                                                         *)
(* However the algorithm violates this property.  This may prevent         *)
(* learners to learn about a chosen value without triggering a new         *)
(* proposal.  In practice the same problem happens with crashes (which are *)
(* not modeled here), and Lamport addresses it in section 2.3.             *)
(***************************************************************************)
Agreement == 
    \A c \in C : [](IsChosen(c, accepted) => 
        (\A d \in C : d # c => [](\neg IsChosen(d, accepted))))

                        
                            


    
    

=============================================================================
\* Modification History
\* Last modified Sun Aug 30 14:01:53 EDT 2015 by nano
\* Created Sat Aug 29 17:37:33 EDT 2015 by nano
