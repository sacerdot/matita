include ../../../Makefile.defs

H=@

REQUIRES = helm-library

MLS = heights.ml
MLIS =
CLEAN =

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

all: heights .depend
	@echo -n

opt: heights.opt $(EXTRAS) .depend.opt
	@echo -n

heights: $(CMIS) $(CMOS) $(EXTRAS) 
	@echo "  OCAMLC $(CMOS)"
	$(H)$(OCAMLC) -o $@ $(CMOS)

heights.opt: $(CMIS) $(CMXS) $(EXTRAS)
	@echo "  OCAMLOPT $(CMXS)"
	$(H)$(OCAMLOPT) -o $@ $(CMXS)

clean:
	$(H)rm -f *.cm[iox] *.a *.o *.output
	$(H)rm -f heights heights.opt $(CLEAN)

.depend: $(MLIS) $(MLS) $(EXTRAS)
	@echo "  OCAMLDEP $(MLIS) $(MLS)"
	$(H)$(OCAMLDEP) $(MLIS) $(MLS) > .depend

.depend.opt: $(MLIS) $(MLS) $(EXTRAS)
	@echo "  OCAMLDEP -native $(MLIS) $(MLS)"
	$(H)$(OCAMLDEP) -native $(MLIS) $(MLS) > .depend.opt

test: heights heights.conf.xml 
	@echo "  HEIGHTS" 
	$(H)$< 1> heights.txt 2> errors.txt

test.opt: heights.opt heights.conf.xml $(PACKAGES:%=%.conf.xml) 
	@echo "  HEIGHTS.OPT" 
	$(H)$< 1> heights.txt 2> errors.txt

export: clean
	$(H)rm -f *~
	@echo "  TAR heights"
	$(H)cd .. && tar --exclude=heights/.svn -czf heights.tgz heights

depend: .depend 

depend.opt: .depend.opt 

%.cmi: %.mli $(EXTRAS)
	@echo "  OCAMLC $<"
	$(H)$(OCAMLC) -c $<
%.cmo %.cmi: %.ml $(EXTRAS) $(LIBRARIES)
	@echo "  OCAMLC $<"
	$(H)$(OCAMLC) -c $<
%.cmx: %.ml $(EXTRAS) $(LIBRARIES_OPT)
	@echo "  OCAMLOPT $<"
	$(H)$(OCAMLOPT) -c $<
%.ml %.mli: %.mly $(EXTRAS) 
	@echo "  OCAMLYACC $<"
	$(H)$(OCAMLYACC) -v $<
%.ml: %.mll $(EXTRAS) 
	@echo "  OCAMLLEX $<"
	$(H)$(OCAMLLEX) $<

include ../../../Makefile.defs

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
