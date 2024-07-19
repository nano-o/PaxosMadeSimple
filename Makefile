APA_RELEASE_URL=https://github.com/informalsystems/apalache/releases/download/v0.44.11/apalache-0.44.11.tgz
APA=apalache-0.44.11
APA_ARCHIVE=$(APA).tgz
TOOLS_JAR=tla2tools.jar
TOOLS_JAR_URL=https://github.com/tlaplus/tlaplus/releases/download/v1.7.3/tla2tools.jar

all: $(APA) $(TOOLS_JAR)

$(APA):
	wget --no-check-certificate --content-disposition $(APA_RELEASE_URL)
	tar -xzf $(APA_ARCHIVE)

$(TOOLS_JAR):
	wget --no-check-certificate --content-disposition -O $@ $(TOOLS_JAR_URL)

tlc: tla2tools.jar PaxosMadeSimple.tla TLCPaxosMadeSimple.tla TLCPaxosMadeSimple.cfg
	java -XX:+UseParallelGC -jar tla2tools.jar -config TLCPaxosMadeSimple.cfg -workers 4 TLCPaxosMadeSimple.tla

pcal: tla2tools.jar PaxosMadeSimple.tla
	java -cp tla2tools.jar pcal.trans PaxosMadeSimple.tla

typecheck: $(APA) Paxos.tla ApaPaxos.tla
	APA=$(APA) ./check.sh -typecheck Paxos

# Don't redownload stuff every time
.PRECIOUS: $(APA) $(TOOLS_JAR)

# check: $(APA) TetraBFT.tla ApaTetraBFT.tla
	# APA=$(APA) ./check.sh -inductive Invariant TetraBFT

.PHONY: tlc
