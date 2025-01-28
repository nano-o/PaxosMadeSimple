JAR=tla2tools.jar
JAR_URL=https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar

$(JAR):
	wget --no-check-certificate --content-disposition -O $@ $(JAR_URL)

tlc: tla2tools.jar PaxosMadeSimple.tla TLCPaxosMadeSimple.tla TLCPaxosMadeSimple.cfg
	java -XX:+UseParallelGC -jar tla2tools.jar -config TLCPaxosMadeSimple.cfg -workers 4 TLCPaxosMadeSimple.tla

pcal: tla2tools.jar PaxosMadeSimple.tla
	java -cp tla2tools.jar pcal.trans PaxosMadeSimple.tla

PaxosMadeSimple.pdf: PaxosMadeSimple.tla tla2tools.jar
	java -cp $(JAR) tla2tex.TLA -shade -latexCommand pdflatex $<

# Don't redownload stuff every time
.PRECIOUS: $(JAR)

.PHONY: tlc
