H=@

REQUIRES = helm-grafite_parser helm-tactics

INTERFACE_FILES = 
IMPLEMENTATION_FILES = $(INTERFACE_FILES:%.mli=%.ml) 
EXTRA_OBJECTS_TO_INSTALL =
EXTRA_OBJECTS_TO_CLEAN = \
	saturate saturate.opt

all: saturate
	$(H)echo -n
opt: saturate.opt
	$(H)echo -n

saturate: saturate_main.ml
	$(H)echo "    OCAMLC $<"
	$(H)$(OCAMLFIND) ocamlc \
		-I ../../tactics/paramodulation/ -thread -package "$(REQUIRES)" -linkpkg -o $@ $<

saturate.opt: saturate_main.ml
	$(H)echo "    OCAMLOPT $<"
	$(H)$(OCAMLFIND) ocamlopt \
		-I ../../tactics/paramodulation/ -thread -package "$(REQUIRES)" -linkpkg -o $@ $<

clean:
	$(H)rm -f *.cm[iox] *.a *.o
	$(H)rm -f saturate saturate.opt

depend:
depend.opt:

include ../../../Makefile.defs
