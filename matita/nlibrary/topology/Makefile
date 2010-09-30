SRC=igft.ma

all: $(SRC:%.ma=%.html)

print: $(SRC:%.ma=%.pdf)

%.pdf: %.html
	# requires http://torisugari.googlepages.com/commandlineprint2
	touch $@
	iceweasel -print file://$$PWD/$< -printmode PDF -printfile ./$@

clean:
	rm *.html *.png *.mdwn

%.html: %.ma convert.awk preamble.xml postamble.xml
	cat preamble.xml > $@
	awk -f convert.awk < $< > $*.mdwn
	markdown < $*.mdwn >> $@
	cat postamble.xml >> $@

