H=@

REQUIRES = mysql helm-metadata

INTERFACE_FILES = 
IMPLEMENTATION_FILES = $(INTERFACE_FILES:%.mli=%.ml) 
EXTRA_OBJECTS_TO_INSTALL =
EXTRA_OBJECTS_TO_CLEAN = \
	table_creator table_creator.opt table_destructor table_destructor.opt

all: table_creator table_destructor
	$(H)echo -n
opt: table_creator.opt table_destructor.opt
	$(H)echo -n

table_creator: table_creator.ml 
	$(H)echo "    OCAMLC $<"
	$(H)$(OCAMLFIND) ocamlc \
		-thread -package mysql,helm-metadata -linkpkg -rectypes -o $@ $<

table_destructor: table_creator
	$(H)ln -f $< $@

table_creator.opt: table_creator.ml
	$(H)echo "    OCAMLOPT $<"
	$(H)$(OCAMLFIND) ocamlopt \
		-thread -package mysql,helm-metadata -linkpkg -rectypes -o $@ $<

table_destructor.opt: table_creator.opt
	$(H)ln  -f $< $@

clean:
	$(H)rm -f *.cm[iox] *.a *.o
	$(H)rm -f table_creator table_creator.opt \
		table_destructor table_destructor.opt

depend: 
	$(H)echo "  OCAMLDEP"
	$(H)ocamldep table_creator.ml > .depend
depend.opt: 
	$(H)echo "  OCAMLDEP -native"
	$(H)ocamldep -native table_creator.ml > .depend.opt

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
