TOOLS_JAR=tla2tools.jar
TOOLS_JAR_URL=https://github.com/tlaplus/tlaplus/releases/download/v1.7.3/tla2tools.jar

$(TOOLS_JAR):
	wget --no-check-certificate --content-disposition -O $@ $(TOOLS_JAR_URL)

tlc: tla2tools.jar PaxosMadeSimple.tla TLCPaxosMadeSimple.tla TLCPaxosMadeSimple.cfg
	java -XX:+UseParallelGC -jar tla2tools.jar -config TLCPaxosMadeSimple.cfg -workers 4 TLCPaxosMadeSimple.tla

# Don't redownload stuff every time
.PRECIOUS: $(TOOLS_JAR)

.PHONY: tlc
