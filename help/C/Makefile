XSLTPROC=xsltproc
XHTML_XSL=http://docbook.sourceforge.net/release/xsl/current/xhtml/docbook.xsl
FO_XSL=http://docbook.sourceforge.net/release/xsl/current/fo/docbook.xsl

all: html txt

.PHONY: html
html: html-stamp
html-stamp: matita.html
	./split.ml $<
	touch $@

TXTS = $(patsubst %.html,%.txt,$(wildcard *.html))
.PHONY: txt
txt: txt-stamp
txt-stamp: html-stamp
	$(MAKE) $(TXTS)
	touch $@

%.txt: %.html
	w3m -dump $< > $@
%.html: %.xml
	xsltproc $(XHTML_XSL) $< | xmllint --format - > $@
%.fo: %.xml
	xsltproc $(FO_XSL) $< | xmllint --format - > $@
%.pdf: %.fo
	fop $< $@
clean:
	rm -f *.html *.fo *.pdf
	rm -rf $(filter-out version.txt,$(wildcard *.txt))
	rm -f *-stamp

