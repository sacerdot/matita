include ../../../Makefile.defs

H=@

REQUIRES = unix str helm-grafite_parser

MLS = types.ml options.ml \
      gallina8Parser.ml gallina8Lexer.ml \
      grafiteParser.ml grafiteLexer.ml \
      grafite.ml engine.ml top.ml
MLIS = gallina8Parser.mli grafiteParser.mli grafite.mli engine.mli
CLEAN = gallina8Parser.ml gallina8Parser.mli gallina8Lexer.ml \
        grafiteParser.ml grafiteParser.mli grafiteLexer.ml

PACKAGES = CoRN

LIBRARIES = $(shell $(OCAMLFIND) query -recursive -predicates "byte $(PREDICATES)" -format "%d/%a" $(REQUIRES))
LIBRARIES_OPT = $(shell $(OCAMLFIND) query -recursive -predicates "native $(PREDICATES)" -format "%d/%a" $(REQUIRES))

CMOS = $(MLS:%.ml=%.cmo)
CMXS = $(MLS:%.ml=%.cmx)
CMIS = $(MLIS:%.mli=%.cmi)
EXTRAS =

OCAMLC = $(OCAMLFIND) ocamlc -thread -package "$(REQUIRES)" -linkpkg -rectypes
OCAMLOPT = $(OCAMLFIND) ocamlopt -thread -package "$(REQUIRES)" -linkpkg -rectypes
OCAMLDEP = $(OCAMLFIND) ocamldep
OCAMLYACC = ocamlyacc
OCAMLLEX = ocamllex

all: transcript .depend
	@echo -n

opt: transcript.opt $(EXTRAS) .depend.opt
	@echo -n

transcript: $(CMIS) $(CMOS) $(EXTRAS) 
	@echo "  OCAMLC $(CMOS)"
	$(H)$(OCAMLC) -o $@ $(CMOS)

transcript.opt: $(CMIS) $(CMXS) $(EXTRAS)
	@echo "  OCAMLOPT $(CMXS)"
	$(H)$(OCAMLOPT) -o $@ $(CMXS)

clean:
	$(H)rm -f *.cm[iox] *.a *.o *.output
	$(H)rm -f transcript transcript.opt $(CLEAN)

.depend: $(MLIS) $(MLS) $(EXTRAS)
	@echo "  OCAMLDEP $(MLIS) $(MLS)"
	$(H)$(OCAMLDEP) $(MLIS) $(MLS) > .depend

.depend.opt: $(MLIS) $(MLS) $(EXTRAS)
	@echo "  OCAMLDEP -native $(MLIS) $(MLS)"
	$(H)$(OCAMLDEP) -native $(MLIS) $(MLS) > .depend.opt

test: transcript transcript.conf.xml $(PACKAGES:%=%.conf.xml) 
	@echo "  TRANSCRIPT $(PACKAGES)" 
	$(H)$< $(PACKAGES)

test.opt: transcript.opt transcript.conf.xml $(PACKAGES:%=%.conf.xml) 
	@echo "  TRANSCRIPT.OPT $(PACKAGES)" 
	$(H)$< $(PACKAGES)

export: clean
	$(H)rm -f *~
	@echo "  TAR transcript"
	$(H)cd .. && tar --exclude=transcript/.svn -czf transcript.tgz transcript

depend: .depend 

depend.opt: .depend.opt 

%.cmi: %.mli $(EXTRAS)
	@echo "  OCAMLC $<"
	$(H)$(OCAMLC) -c $<
%.cmo %.cmi: %.ml $(EXTRAS) $(LIBRARIES)
	@echo "  OCAMLC $<"
	$(H)$(OCAMLC) -c $<
%.o %.cmx %.cmi: %.ml $(EXTRAS) $(LIBRARIES_OPT)
	@echo "  OCAMLOPT $<"
	$(H)$(OCAMLOPT) -c $<
%.ml %.mli: %.mly $(EXTRAS) 
	@echo "  OCAMLYACC $<"
	$(H)$(OCAMLYACC) -v $<
%.ml: %.mll $(EXTRAS) 
	@echo "  OCAMLLEX $<"
	$(H)$(OCAMLLEX) $<

ifeq ($(MAKECMDGOALS),)
  include .depend   
endif

ifeq ($(MAKECMDGOALS), all)
  include .depend   
endif

ifeq ($(MAKECMDGOALS), opt)
  include .depend.opt   
endif

ifeq ($(MAKECMDGOALS), test)
  include .depend   
endif

ifeq ($(MAKECMDGOALS), test.opt)
  include .depend.opt   
endif
