TOOLS_JAR=tla2tools.jar
TOOLS_JAR_URL=https://github.com/tlaplus/tlaplus/releases/download/v1.7.3/tla2tools.jar

$(TOOLS_JAR):
	wget --no-check-certificate --content-disposition -O $@ $(TOOLS_JAR_URL)

tlc: tla2tools.jar PaxosMadeSimple.tla PaxosMadeSimple.cfg
	java -XX:+UseParallelGC -jar tla2tools.jar -config PaxosMadeSimple.cfg -workers 4 PaxosMadeSimple.tla

# Don't redownload stuff every time
.PRECIOUS: $(TOOLS_JAR)

.PHONY: tlc
