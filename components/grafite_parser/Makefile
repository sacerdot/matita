PACKAGE = grafite_parser
PREDICATES =

INTERFACE_FILES = 			\
	dependenciesParser.mli  	\
	grafiteParser.mli		\
	cicNotation2.mli		\
	nEstatus.mli			\
	grafiteDisambiguate.mli 	\
	print_grammar.mli 		\
	$(NULL)
IMPLEMENTATION_FILES = $(INTERFACE_FILES:%.mli=%.ml)

all: test_parser test_dep
clean: clean_tests

# <cross> cross compatibility among ocaml 3.09 and ocaml 3.08, to be removed as
# soon as we have ocaml 3.09 everywhere and "loc" occurrences are replaced by
# "_loc" occurrences
UTF8DIR = $(shell $(OCAMLFIND) query helm-syntax_extensions)
ULEXDIR = $(shell $(OCAMLFIND) query ulex08)
MY_SYNTAXOPTIONS = -pp "camlp5o -I $(UTF8DIR) -I $(ULEXDIR) pa_extend.cmo pa_ulex.cma pa_unicode_macro.cma -loc loc"
grafiteParser.cmo: SYNTAXOPTIONS = $(MY_SYNTAXOPTIONS)
grafiteParser.cmx: SYNTAXOPTIONS = $(MY_SYNTAXOPTIONS)
depend: SYNTAXOPTIONS = $(MY_SYNTAXOPTIONS)
depend.opt: SYNTAXOPTIONS = $(MY_SYNTAXOPTIONS)
# </cross>
#
grafiteParser.cmo: OCAMLC = $(OCAMLC_P4)
grafiteParser.cmx: OCAMLOPT = $(OCAMLOPT_P4)

clean_tests:
	rm -f test_parser{,.opt} test_dep{,.opt} print_grammar{,.opt}

LOCAL_LINKOPTS = -package helm-$(PACKAGE) -linkpkg
test: test_parser print_grammar test_dep
test_parser: test_parser.ml $(PACKAGE).cma
	@echo "  OCAMLC $<"
	@$(OCAMLC) $(LOCAL_LINKOPTS) -o $@ $<
print_grammar: print_grammar.ml $(PACKAGE).cma
	@echo "  OCAMLC $<"
	@$(OCAMLC) $(LOCAL_LINKOPTS) -o $@ $<
test_dep: test_dep.ml $(PACKAGE).cma
	@echo "  OCAMLC $<"
	@$(OCAMLC) $(LOCAL_LINKOPTS) -o $@ $<

include ../../Makefile.defs
include ../Makefile.common
