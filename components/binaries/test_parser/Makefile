H=@

REQUIRES = str helm-grafite_parser

INTERFACE_FILES = 
IMPLEMENTATION_FILES = $(INTERFACE_FILES:%.mli=%.ml) 
EXTRA_OBJECTS_TO_INSTALL =
EXTRA_OBJECTS_TO_CLEAN = \
	test_parser test_parser.opt test_dep test_dep.opt print_grammar print_grammar.opt

all: test_parser test_dep print_grammar
	$(H)echo -n
opt: test_parser.opt test_dep.opt print_grammar.opt
	$(H)echo -n

test_parser: test_parser.ml
	$(H)echo "    OCAMLC $<"
	$(H)$(OCAMLFIND) ocamlc \
		-I ../../tactics/paramodulation/ -rectypes -thread -package "$(REQUIRES)" -linkpkg -o $@ $<

test_parser.opt: test_parser.ml
	$(H)echo "    OCAMLOPT $<"
	$(H)$(OCAMLFIND) ocamlopt \
		-I ../../tactics/paramodulation/ -thread -package "$(REQUIRES)" -linkpkg -o $@ $<

test_dep: test_dep.ml
	$(H)echo "    OCAMLC $<"
	$(H)$(OCAMLFIND) ocamlc \
		-I ../../tactics/paramodulation/ -rectypes -thread -package "$(REQUIRES)" -linkpkg -o $@ $<

test_dep.opt: test_dep.ml
	$(H)echo "    OCAMLOPT $<"
	$(H)$(OCAMLFIND) ocamlopt \
		-I ../../tactics/paramodulation/ -thread -package "$(REQUIRES)" -linkpkg -o $@ $<

print_grammar: print_grammar.ml
	$(H)echo "    OCAMLC $<"
	$(H)$(OCAMLFIND) ocamlc \
		-I ../../tactics/paramodulation/ -rectypes -thread -package "$(REQUIRES)" -linkpkg -o $@ $<

print_grammar.opt: print_grammar.ml
	$(H)echo "    OCAMLOPT $<"
	$(H)$(OCAMLFIND) ocamlopt \
		-I ../../tactics/paramodulation/ -thread -package "$(REQUIRES)" -linkpkg -o $@ $<

clean:
	$(H)rm -f *.cm[iox] *.a *.o
	$(H)rm -f test_parser test_parser.opt test_dep test_dep.opt print_grammar print_grammar.opt

depend:
depend.opt:

include ../../../Makefile.defs
