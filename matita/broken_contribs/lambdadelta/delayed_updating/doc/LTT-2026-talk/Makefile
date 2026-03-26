H = @

MAINS = ltt-2026-talk-i ltt-2026-talk

all: $(MAINS:%=%.pdf)

clean:
	$(H)latexmk -C

%.pdf: %.tex *.tex *.sty
	$(H)latexmk -pdf $<
