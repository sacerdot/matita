H=@

REQUIRES = helm-content_pres

INTERFACE_FILES = 
IMPLEMENTATION_FILES = $(INTERFACE_FILES:%.mli=%.ml) 
EXTRA_OBJECTS_TO_INSTALL =
EXTRA_OBJECTS_TO_CLEAN = \
	test_lexer test_lexer.opt

all: test_lexer
	$(H)echo -n
opt: test_lexer.opt
	$(H)echo -n

test_lexer: test_lexer.ml
	$(H)echo "    OCAMLC $<"
	$(H)$(OCAMLFIND) ocamlc \
		-I ../../tactics/paramodulation/ -rectypes -thread -package "$(REQUIRES)" -linkpkg -o $@ $<

test_lexer.opt: test_lexer.ml
	$(H)echo "    OCAMLOPT $<"
	$(H)$(OCAMLFIND) ocamlopt \
		-I ../../tactics/paramodulation/ -thread -package "$(REQUIRES)" -linkpkg -o $@ $<

clean:
	$(H)rm -f *.cm[iox] *.a *.o
	$(H)rm -f test_lexer test_lexer.opt

depend:
depend.opt:

include ../../../Makefile.defs
