
include ../../../Makefile.defs

XSLTPROC=xsltproc
XHTML_XSL=xsl/matita-xhtml.xsl
MAIN=matita.xml
DEPS := $(wildcard *.xml)

DESTDIR = /usr/local/share/doc/matita/

all: quickref-stamp html-stamp pdf-stamp

quickref-stamp: tactics_quickref.xml declarative_tactics_quickref.xml
	touch $@

tactics_quickref.xml: xsl/tactic_quickref.xsl sec_tactics.xml
	$(XSLTPROC) --param declarative "''" $< matita.xml > $@
declarative_tactics_quickref.xml: xsl/tactic_quickref.xsl sec_declarative_tactics.xml
	$(XSLTPROC) --param declarative "'declarative_'" $< matita.xml > $@

html: quickref-stamp html-stamp
html-stamp: $(MAIN) $(DEPS) $(XHTML_XSL)
	$(XSLTPROC) $(XHTML_XSL) $<
	touch $@

pdf: quickref-stamp pdf-stamp
pdf-stamp: $(patsubst %.xml,%.pdf,$(MAIN))
	touch $@

%.pdf: %.xml
	dblatex -rscripts/fix-symbols.sh -tpdf $< 
%.dvi: %.xml
	dblatex -rscripts/fix-symbols.sh -tdvi $<
%.ps: %.xml
	dblatex -rscripts/fix-symbols.sh -tps $<

install: install-html install-pdf
install-pdf: pdf-stamp
	mkdir -p $(DESTDIR)/pdf
	cp matita.pdf $(DESTDIR)/pdf

install-html: html-stamp 
	mkdir -p $(DESTDIR)/html
	cp *.html *.css $(DESTDIR)/html
	test -d $(DESTDIR)/html/figures || mkdir $(DESTDIR)/html/figures
	cp figures/* $(DESTDIR)/html/figures/

clean:
	rm -f *.html *.pdf *.ps *.dvi *.tex
	rm -f *-stamp 

