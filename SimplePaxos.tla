-------------------------------- MODULE SimplePaxos -------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS P, C

VARIABLES
    proposalNumber,
    proposedCommand,
    accepted,
    lastPromise,
    network,
    chosen

vars == <<proposalNumber, proposedCommand, accepted, 
    lastPromise, network, chosen>>
    
Proposal == [command : C, number: Nat]

Msg(type, Payload) == [type : {type}, payload : Payload]

Msgs == 
    [   type : {"prepare"}, 
        number : Nat ] 
    \cup
    [   type : {"prepare-response"}, 
        proposal: Proposal \cup {<<>>}, 
        number: Nat, 
        from: P ] 
    \cup
    [   type: {"propose"},
        proposal : Proposal ]

TypeInvariant ==
    \A p \in P :
        /\  proposalNumber[p] \in Nat
        /\  proposedCommand[p] \in C \cup {"none"}
        /\  accepted[p] \in Proposal  \cup {<<>>}
        /\  lastPromise[p] \in Nat
        /\  network \in SUBSET Msgs
        /\  chosen \in SUBSET C

Init == 
    /\  proposalNumber = [p \in P |-> 0]
    /\  proposedCommand = [p \in P |-> "none"]
    /\  accepted = [p \in P |-> <<>>]
    /\  lastPromise = [p \in P |-> 0]
    /\  network = {}
    /\  chosen = {}

Prepare(p) == \E n \in Nat :
    /\  proposalNumber[p] = 0
    /\  \A q \in P : proposalNumber[q] # n 
    /\  proposalNumber' = [proposalNumber EXCEPT ![p] = n]
    /\  network' = network \cup {[type |-> "prepare", number |-> n]}
    /\  UNCHANGED <<accepted, lastPromise, proposedCommand, chosen>>

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
    /\  UNCHANGED <<proposalNumber, accepted, proposedCommand, chosen>>

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
    /\  proposedCommand[p] = "none"
    /\  \E Q \in MajoritySets :   
            /\  \A q \in Q : \E m \in network :
                    /\  IsPrepareResponse(p,m)
                    /\  m.from = q
            /\  LET proposals == ProposalsInPrepareResponses(p, Q)
                IN  IF  proposals # {}
                    THEN    LET c == HighestProposal(proposals).command
                            IN  /\  SendProposal(p, c)
                                /\  proposedCommand' = 
                                        [proposedCommand EXCEPT ![p] = c]
                    ELSE
                        \E c \in C : 
                            /\  SendProposal(p, c)
                            /\  proposedCommand' = 
                                        [proposedCommand EXCEPT ![p] = c]
    /\  UNCHANGED <<proposalNumber, accepted, lastPromise, chosen>> 

IsChosen(c, acc) ==
    \E Q \in MajoritySets : \A q \in Q :
        /\  acc[q] # <<>>
        /\  acc[q].command = c
        
Accept(p) ==
    /\  \E m \in network :
            /\  m.type = "propose"
            /\  m.proposal.number \geq lastPromise[p]
            /\  accepted' = [accepted EXCEPT ![p] = m.proposal]
            /\  IF  IsChosen(m.proposal.command, accepted')
                THEN chosen' = chosen \cup {m.proposal.command}
                ELSE UNCHANGED chosen
    /\  UNCHANGED  <<network, proposalNumber, lastPromise, proposedCommand>>

Next == \E p \in P :
    \/  Prepare(p)
    \/  PrepareReponse(p)
    \/  Propose(p)
    \/  Accept(p)


Agreement == 
    \A c \in C : [](IsChosen(c, accepted) => []IsChosen(c, accepted))

                        
                            


    
    

=============================================================================
\* Modification History
\* Last modified Sun Aug 30 01:21:27 EDT 2015 by nano
\* Created Sat Aug 29 17:37:33 EDT 2015 by nano
