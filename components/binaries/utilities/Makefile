H=@

UTILITIES = create_environment parse_library list_uris test_library
UTILITIES_OPT = $(patsubst %,%.opt,$(UTILITIES))
LINKOPTS = -linkpkg -rectypes -thread
LIBS = helm-cic_proof_checking
OCAMLC = $(OCAMLFIND) ocamlc $(LINKOPTS) -package $(LIBS)
OCAMLOPT = $(OCAMLFIND) opt $(LINKOPTS) -package $(LIBS)
all: $(UTILITIES)
	$(H)echo -n
opt: $(UTILITIES_OPT)
	$(H)echo -n
%: %.ml
	$(H)echo "    OCAMLC $<"
	$(H)$(OCAMLC) -o $@ $<
%.opt: %.ml
	$(H)echo "    OCAMLOPT $<"
	$(H)$(OCAMLOPT) -o $@ $<
clean:
	rm -f $(UTILITIES) $(UTILITIES_OPT) *.cm[iox] *.o
depend: 
	$(H)echo "  OCAMLDEP"
	$(H)ocamldep extractor.ml extractor_manager.ml > .depend
depend.opt: 
	$(H)echo "  OCAMLDEP -native"
	$(H)ocamldep -native extractor.ml extractor_manager.ml > .depend.opt
	
ifeq ($(MAKECMDGOALS),)
  include .depend   
endif

ifeq ($(MAKECMDGOALS), all)
  include .depend   
endif

ifeq ($(MAKECMDGOALS), opt)
  include .depend.opt   
endif
	
include ../../../Makefile.defs

