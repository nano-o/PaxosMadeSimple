# PaxosMadeSimple
A TLA+ formalization of the algorithm described in "Paxos Made Simple"

Can be model-checked by opening the spec in the TLA toolbox and instructing the toolbox to import the model named "Model_1".

Some people noted that there is a problem in the algorithm as described in the paper:
http://stackoverflow.com/questions/29880949/contradiction-in-lamports-paxos-made-simple-paper
To have TLC find the problem, remove or comment out the line below the comment that reads "One way to fix the "bug" reported on stackoverflow:".
