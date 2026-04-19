H = @

MAINS = ltt-2026-presentation ltt-2026-slides

all: $(MAINS:%=%.pdf)

clean:
	$(H)latexmk -C

%.pdf: %.tex *.tex *.sty
	$(H)latexmk -pdf $<
