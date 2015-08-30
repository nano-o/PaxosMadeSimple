# PaxosMadeSimple
A TLA+ formalization of the algorithm described in "Paxos Made Simple"

Can be model-checked with 3 processes, 2 commands, and 1..3 substituted for Nat by just importing the model "Model_1" in the TLA toolbox.

Some people noted that there is a problem in the algorithm as described in the paper:
http://stackoverflow.com/questions/29880949/contradiction-in-lamports-paxos-made-simple-paper
To have TLC find the problem, uncomment the line below the comment that reads "One way to fix the "bug" reported on stackoverflow:".
