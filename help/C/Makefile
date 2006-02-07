XSLTPROC=xsltproc
XHTML_XSL=http://docbook.sourceforge.net/release/xsl/current/xhtml/docbook.xsl
FO_XSL=http://docbook.sourceforge.net/release/xsl/current/fo/docbook.xsl
all:
%.html: %.xml
	xsltproc $(XHTML_XSL) $< > $@
%.fo: %.xml
	xsltproc $(FO_XSL) $< > $@
%.pdf: %.fo
	fop $< $@
clean:
	rm -f *.html *.fo *.pdf
