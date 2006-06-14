
include ../../../Makefile.defs

XSLTPROC=xsltproc
XHTML_XSL=xsl/matita-xhtml.xsl
FO_XSL=xsl/matita-fo.xsl
TEX_XSL=xsl/matita-tex.xsl
TEX_UNICODE_PATH=$(SRCROOT)/share/texmf/unicode
TEX_ENV=TEXINPUTS=.:$(TEX_UNICODE_PATH):$(TEX_UNICODE_PATH)/data:
MAIN=matita.xml
DEPS := $(wildcard *.xml)

DESTDIR = /usr/local/share/doc/matita/

all: quickref

quickref: tactic_quickref.xml
tactic_quickref.xml: xsl/tactic_quickref.xsl sec_tactics.xml
	$(XSLTPROC) $< matita.xml > tactic_quickref.xml

# one of: "fop", "pdflatex"
PDF_METHOD=pdflatex

# one of: "docbook2tex", "xsl"
TEX_METHOD=xsl

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
html-stamp: $(MAIN) $(DEPS) $(XHTML_XSL)
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
	w3m -dump -no-graph $< > $@

# PDF generation

pdf: pdf-stamp
pdf-stamp: $(patsubst %.xml,%.pdf,$(MAIN))
	touch $@

%.fo: %.xml
	xsltproc $(FO_XSL) $< | xmllint --format - > $@
ifeq ($(TEX_METHOD),docbook2tex)
%.tex: %.xml $(DEPS)
	docbook2tex $<
else ifeq ($(TEX_METHOD),xsl)
%.tex: %.xml $(TEX_XSL) $(DEPS)
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

# installation

install: install-html
install-html: html-stamp
	cp *.html *.css $(DESTDIR)
	test -d $(DESTDIR)/figures || mkdir $(DESTDIR)/figures
	cp figures/* $(DESTDIR)/figures/

# shotcuts

tex: $(patsubst %.xml,%.tex,$(MAIN))
dvi: $(patsubst %.xml,%.dvi,$(MAIN))
ps: $(patsubst %.xml,%.ps,$(MAIN))

.PRECIOUS: matita.tex matita.dvi

