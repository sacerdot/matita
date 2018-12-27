PACKAGE = ng_library
PREDICATES =

INTERFACE_FILES = \
	nCicLibrary.mli

IMPLEMENTATION_FILES = \
  $(INTERFACE_FILES:%.mli=%.ml)
EXTRA_OBJECTS_TO_INSTALL = 
EXTRA_OBJECTS_TO_CLEAN =

all:
%: %.ml $(PACKAGE).cma
	$(OCAMLC) -package helm-$(PACKAGE) -linkpkg -o $@ $<
all.opt opt:
%.opt: %.ml $(PACKAGE).cmxa
	$(OCAMLOPT) -package helm-$(PACKAGE) -linkpkg -o $@ $<

include ../../Makefile.defs
include ../Makefile.common

