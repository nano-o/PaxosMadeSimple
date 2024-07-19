--------- MODULE TLCPaxos ------

EXTENDS Paxos, TLC

CONSTANTS
    v1, v2,
    a1, a2, a3

TLCValue == {v1,v2}
TLCAcceptor == {a1,a2,a3}
TLCQuorum == {{a1,a2},{a1,a3},{a2,a3}}
TLCBallot == 0..3

Symm == Permutations(TLCAcceptor) \cup Permutations(TLCValue)

================================================