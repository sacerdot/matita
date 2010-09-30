PACKAGE = tptp_grafite
PREDICATES = 

INTERFACE_FILES= parser.mli parserTHF.mli tptp2grafite.mli

IMPLEMENTATION_FILES = ast.ml lexer.ml astTHF.ml lexerTHF.ml $(INTERFACE_FILES:%.mli=%.ml)
EXTRA_OBJECTS_TO_INSTALL = 
EXTRA_OBJECTS_TO_CLEAN =

TPTPDIR= /home/$(USER)/work-area/TPTP-v4.0.1/

all: tptp2grafite mainTHF
clean: clean_tests clean_generated

clean_generated:
	rm -f parser.mli parser.ml parserTHF.mli parserTHF.ml 
	rm -f lexer.ml lexerTHF.ml

clean_tests:
	rm -f tptp2grafite

lexer.cmo: parser.cmi
lexer.cmx: parser.cmi
lexerTHF.cmo: parserTHF.cmi
lexerTHF.cmx: parserTHF.cmi

%.mli %.ml: %.mly
	ocamlyacc $*.mly
%.ml:%.mll
	ocamllex $*.mll

LOCAL_LINKOPTS = -package helm-$(PACKAGE) -linkpkg
tptp2grafite: main.ml tptp_grafite.cma
	@echo "  OCAMLC $<"
	@$(OCAMLC) $(LOCAL_LINKOPTS) -o $@ $<

mainTHF: mainTHF.ml tptp_grafite.cma 
	@echo "  OCAMLC $<"
	@$(OCAMLC) $(LOCAL_LINKOPTS) -o $@ $<

test: tptp2grafite mainTHF

testall: tptp2grafite
	for X in `cat unit_equality_problems`; do\
		cat $(TPTPDIR)/$$X | ./tptp2grafite || echo ERROR PARSING $$X;\
	done

generate-%:
	for X in `cat $*`; do\
		./tptp2grafite -tptppath $(TPTPDIR) $$X.p \
		> ../../matita/tests/TPTP/$$X.ma || echo Failed: $$X; \
	done

ngenerate-%:
	for X in `cat $*`; do\
		./tptp2grafite -ng -tptppath $(TPTPDIR) $$X.p \
		> ../../matita/contribs/ng_TPTP/$$X.ma || echo Failed: $$X; \
	done

parse-%:
	for X in `cat $*`; do\
	  echo "Parsing $$X"; \
		./tptp2grafite -tptppath $(TPTPDIR) $$X.p \
		> /dev/null || echo Failed: $$X; \
	done

thf:
	rm -rf THF
	mkdir THF
	for x in `cat thf_problems`; do\
		echo $$x;\
		./mainTHF -tptppath $(TPTPDIR) $$x.p > THF/$$x.ma;\
	done

include ../../Makefile.defs
include ../Makefile.common

