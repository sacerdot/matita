XSLTPROC=xsltproc
XHTML_XSL=matita-xhtml.xsl
FO_XSL=matita-fo.xsl
MAIN=matita.xml

all: html txt

# XHTMLs generation

.PHONY: html
html: html-stamp
html-stamp: $(MAIN)
	xsltproc $(XHTML_XSL) $<
	touch $@

# TXTs generation

TXTS = $(patsubst %.html,%.txt,$(wildcard *.html))
.PHONY: txt
txt: txt-stamp
txt-stamp: html-stamp
	$(MAKE) $(TXTS)
	touch $@
%.txt: %.html
	w3m -dump $< > $@

# PDF generation

pdf: pdf-stamp
pdf-stamp: $(patsubst %.xml,%.pdf,$(MAIN))
	touch $@
%.fo: %.xml
	xsltproc $(FO_XSL) $< | xmllint --format - > $@
%.pdf: %.fo
	fop $< $@
clean:
	rm -f *.html *.fo *.pdf
	rm -rf $(filter-out version.txt,$(wildcard *.txt))
	rm -f *-stamp

