H=@

all: extractor extractor_manager 
	$(H)echo -n
opt: extractor.opt extractor_manager.opt
	$(H)echo -n

clean:
	rm -f *.cm[ixo] *.[ao] extractor extractor.opt *.err *.out extractor_manager extractor_manager.opt

extractor: extractor.ml
	$(H)echo "    OCAMLC $<"
	$(H)$(OCAMLFIND) ocamlc \
		-thread -package mysql,helm-metadata,helm-library -linkpkg -rectypes -o $@ $<

extractor.opt: extractor.ml
	$(H)echo "    OCAMLOPT $<"
	$(H)$(OCAMLFIND) ocamlopt \
		-thread -package mysql,helm-metadata,helm-library -linkpkg -rectypes -o $@ $<

extractor_manager: extractor_manager.ml
	$(H)echo "    OCAMLC $<"
	$(H)$(OCAMLFIND) ocamlc \
		-thread -package mysql,helm-metadata,helm-library -linkpkg -rectypes -o $@ $<

extractor_manager.opt: extractor_manager.ml
	$(H)echo "    OCAMLOPT $<"
	$(H)$(OCAMLFIND) ocamlopt \
		-thread -package mysql,helm-metadata,helm-library -linkpkg -rectypes -o $@ $<

export: extractor.opt extractor_manager.opt
	 nice -n 20 \
	 	time \
		./extractor_manager.opt 1>export.out 2>export.err
	
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
