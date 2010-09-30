PACKAGE = cic_disambiguation
NOTATIONS = number
INTERFACE_FILES =		\
	cicDisambiguate.mli     \
	disambiguateChoices.mli
IMPLEMENTATION_FILES = \
	$(patsubst %.mli, %.ml, $(INTERFACE_FILES)) \
	$(patsubst %,%_notation.ml,$(NOTATIONS))

all:

clean:
distclean:
	rm -f macro_table.dump

include ../../Makefile.defs
include ../Makefile.common

OCAMLARCHIVEOPTIONS += -linkall

