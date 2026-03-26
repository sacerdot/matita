.PHONY: clean all dist

all:
	latexmk -pdf example.tex

clean:
	latexmk -C

dist: clean
	zip eptcsstyle.zip generic.bib eptcs.cls *.bst example.tex

out:
	zip ltt-2026-13.zip eptcs.bst eptcs.cls example.tex example.bbl festschrift.bib
