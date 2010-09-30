PACKAGE = ng_library
PREDICATES =

INTERFACE_FILES = \
	nCic2OCic.mli \
	oCic2NCic.mli  \
	nCicLibrary.mli

IMPLEMENTATION_FILES = \
  $(INTERFACE_FILES:%.mli=%.ml)
EXTRA_OBJECTS_TO_INSTALL = 
EXTRA_OBJECTS_TO_CLEAN =
%.cmo: OCAMLOPTIONS += -w Ae
%.cmi: OCAMLOPTIONS += -w Ae
%.cmx: OCAMLOPTIONS += -w Ae

all: rt check
%: %.ml $(PACKAGE).cma
	$(OCAMLC) -package helm-$(PACKAGE) -linkpkg -o $@ $<
all.opt opt: rt.opt check.opt
%.opt: %.ml $(PACKAGE).cmxa
	$(OCAMLOPT) -package helm-$(PACKAGE) -linkpkg -o $@ $<

include ../../Makefile.defs
include ../Makefile.common

