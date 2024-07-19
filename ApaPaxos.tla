---------- MODULE ApaPaxos ----------

Acceptor == {"A1_OF_ACCEPTOR", "A2_OF_ACCEPTOR", "A3_OF_ACCEPTOR"}
Value == {"V1_OF_VALUE", "V2_OF_VALUE"}
Quorum == {{"A1_OF_ACCEPTOR", "A2_OF_ACCEPTOR"}, {"A1_OF_ACCEPTOR", "A3_OF_ACCEPTOR"}, {"A2_OF_ACCEPTOR", "A3_OF_ACCEPTOR"}}
\* We also need to substitue some operators and we have to do the in a TLC cfg file
    
VARIABLES 
    \* @type: ACCEPTOR -> Int;
    maxBal,
    \* @type: ACCEPTOR -> Int;
    maxVBal,
    \* @type: ACCEPTOR -> VALUE;
    maxVVal,
    \* @type: Set(Int);
    1aMsgs,
    \* @type: Set({acc : ACCEPTOR, bal : Int, mbal : Int, mval : VALUE});
    1bMsgs,
    \* @type: Set({bal : Int, val : VALUE});
    2aMsgs,
    \* @type: Set({acc : ACCEPTOR, bal : Int, val : VALUE});
    2bMsgs

INSTANCE Paxos

===============================================