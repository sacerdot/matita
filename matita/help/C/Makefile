XSLTPROC=xsltproc
XHTML_XSL=xsl/matita-xhtml.xsl
MAIN=matita.xml
DEPS := $(wildcard *.xml)

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
	cp *.css html
	mv *.html html
	cp -R figures/* html/figures/
	touch $@

pdf: quickref-stamp pdf-stamp
pdf-stamp: $(patsubst %.xml,%.pdf,$(MAIN))
	touch $@

%.pdf: %.xml
	dblatex -r scripts/fix-symbols.sh -t pdf $< 
%.dvi: %.xml
	dblatex -r scripts/fix-symbols.sh -t dvi $<
%.ps: %.xml
	dblatex -r scripts/fix-symbols.sh -t ps $<

clean:
	rm -f html/*.html html/*.css html/figures/* *.pdf *.ps *.dvi *.tex
	rm -f *-stamp 
