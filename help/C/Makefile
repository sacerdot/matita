
include ../../../Makefile.defs

XSLTPROC=xsltproc
XHTML_XSL=matita-xhtml.xsl
FO_XSL=matita-fo.xsl
TEX_XSL=matita-tex.xsl
TEX_UNICODE_PATH=$(SRCROOT)/share/texmf/unicode
TEX_ENV=TEXINPUTS=.:$(TEX_UNICODE_PATH):$(TEX_UNICODE_PATH)/data:
MAIN=matita.xml
DEPENDENCES = \
	legal.xml \
	sec_install.xml \
	sec_gettingstarted.xml \
	sec_intro.xml \
	sec_terms.xml \
	sec_tactics.xml \
	sec_tacticals.xml \
	sec_commands.xml \
	sec_usernotation.xml

# one of: "fop", "pdflatex"
PDF_METHOD=pdflatex

# one of: "docbook2tex", "xsl"
TEX_METHOD=xsl

all: html txt

clean:
	rm -f *.html *.fo *.pdf
	rm -rf $(filter-out version.txt,$(wildcard *.txt))
	rm -f *-stamp
	rm -f matita.out matita.log matita.glo matita.dvi matita.idx
	rm -f matita.aux matita.tex

# test (dumb implementation)
test:
	SP_ENCODING=UTF-8 docbook2txt matita.xml

# XHTMLs generation

.PHONY: html
html: html-stamp
html-stamp: $(MAIN) $(DEPENDENCES)
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
ifeq ($(TEX_METHOD),docbook2tex)
%.tex: %.xml
	docbook2tex $<
else ifeq ($(TEX_METHOD),xsl)
%.tex: %.xml $(TEX_XSL)
	xsltproc $(TEX_XSL) $< > $@
endif

ifeq ($(PDF_METHOD),fop)
%.pdf: %.fo
	fop $< $@
else ifeq ($(PDF_METHOD),pdflatex)
%.pdf: %.tex
	$(TEX_ENV) pdflatex $<
endif

%.dvi: %.tex
	$(TEX_ENV) latex $<
%.ps: %.dvi
	dvips $<

.PRECIOUS: matita.tex

