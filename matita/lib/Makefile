all:
	touch extraction.ma
	EXTRACT_HASKELL=1 ~/unison_homes/mowgli/matita1.0-reallyfresh/matita/matitac extraction.ma 2> /tmp/foo.hs
	cat preamble.hs /tmp/foo.hs > extraction.hs

.PHONY: all

# ghci extraction.hs
