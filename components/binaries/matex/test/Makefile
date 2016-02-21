LATEX  = latex
DVIPS  = dvips
BIBTEX = bibtex
PSPDF  = ps2pdf -dEmbedAllFonts=true -dPDFSETTINGS=/prepress
UNLOG  = ./unlog.pl

MAIN = test

SOURCES = $(shell cat Make) $(shell cat Make.objs)

all: $(MAIN).dvi 

ps: $(MAIN).ps

pdf: $(MAIN).pdf

tar: $(MAIN).tar

again:
	$(MAKE) --no-print-directory -B

clean:
	$(RM) *.log *.dvi *.aux *.spl *.ps *.blg *.pdf *.tar *~

bibtex: $(MAIN).log
	$(BIBTEX) $(MAIN)

$(MAIN).dvi $(MAIN).log $(MAIN).aux: $(MAIN).tex $(SOURCES)
	$(LATEX) $<

$(MAIN).ps: $(MAIN).dvi 
	$(DVIPS) $<

$(MAIN).pdf: $(MAIN).ps
	$(PSPDF) $<

$(MAIN).tar: $(MAIN).log
	$(UNLOG) $< $@

objs.tex:
	@sed "s/\(.*\).tex/\\\\input{\1}/" Make.objs > $@
