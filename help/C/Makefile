XSLTPROC=xsltproc
XHTML_XSL=matita-xhtml.xsl
FO_XSL=matita-fo.xsl
TEX_XSL=matita-tex.xsl
MAIN=matita.xml

# one of "fop", "pdflatex"
PDF_METHOD=pdflatex

all: html txt

clean:
	rm -f *.html *.fo *.pdf
	rm -rf $(filter-out version.txt,$(wildcard *.txt))
	rm -f *-stamp
	rm -f matita.out matita.log matita.glo matita.dvi matita.idx
	rm -f matita.aux matita.tex

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
%.tex: %.xml
	xsltproc $(TEX_XSL) $< > $@

ifeq ($(PDF_METHOD),fop)
%.pdf: %.fo
	fop $< $@
else ifeq ($(PDF_METHOD),pdflatex)
%.pdf: %.tex
	pdflatex $<
endif

