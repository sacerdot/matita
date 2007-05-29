export SHELL=/bin/bash

include ../Makefile.defs

NULL =
H=@

OCAML_FLAGS = -pp $(CAMLP4O)
PKGS = -package "$(MATITA_REQUIRES)"
CPKGS = -package "$(MATITA_CREQUIRES)"
OCAML_THREADS_FLAGS = -thread
OCAML_DEBUG_FLAGS = -g
#OCAML_PROF=p -p a
#OCAMLOPT_DEBUG_FLAGS = -p
OCAMLC_FLAGS = $(OCAML_FLAGS) $(OCAML_THREADS_FLAGS)
OCAMLC = $(OCAMLFIND) ocamlc$(OCAML_PROF) $(OCAMLC_FLAGS) $(OCAML_DEBUG_FLAGS)
OCAMLOPT = $(OCAMLFIND) opt $(OCAMLC_FLAGS) $(OCAMLOPT_DEBUG_FLAGS)
OCAMLDEP = $(OCAMLFIND) ocamldep $(OCAML_FLAGS)
INSTALL_PROGRAMS= matita matitac
INSTALL_PROGRAMS_LINKS_MATITA= cicbrowser 
INSTALL_PROGRAMS_LINKS_MATITAC= matitadep matitamake matitaclean matitaprover matitawiki

MATITA_FLAGS = -noprofile
NODB=false
ifeq ($(NODB),true)
	MATITA_FLAGS += -nodb
endif

MLI = \
	lablGraphviz.mli	\
	matitaTypes.mli		\
	matitaMisc.mli		\
	matitamakeLib.mli	\
	matitaInit.mli		\
	matitaExcPp.mli 	\
	matitaEngine.mli	\
	applyTransformation.mli	\
	matitacLib.mli		\
	matitaprover.mli        \
	matitaGtkMisc.mli	\
	matitaScript.mli	\
	matitaMathView.mli 	\
	matitaGui.mli		\
	matitaAutoGui.cmo		\
	$(NULL)
CMLI =				\
	matitaTypes.mli		\
	matitaMisc.mli		\
	matitamakeLib.mli	\
	matitaInit.mli		\
	matitaExcPp.mli 	\
	matitaEngine.mli	\
	applyTransformation.mli	\
	matitacLib.mli		\
	matitaWiki.mli		\
	matitaprover.mli        \
	$(NULL)
MAINCMLI =			\
	matitadep.mli		\
	matitaclean.mli		\
	matitamake.mli		\
	gragrep.mli 		\
	$(NULL)
# objects for matita (GTK GUI)
ML = buildTimeConf.ml matitaGeneratedGui.ml $(MLI:%.mli=%.ml)
# objects for matitac (batch compiler)
CML = buildTimeConf.ml $(CMLI:%.mli=%.ml)
MAINCML = $(MAINCMLI:%.mli=%.ml)
	
PROGRAMS_BYTE = \
	matita matitac cicbrowser matitadep matitaclean \
	matitamake matitaprover matitawiki
PROGRAMS = $(PROGRAMS_BYTE) matitatop
PROGRAMS_OPT = $(patsubst %,%.opt,$(PROGRAMS_BYTE))
NOINST_PROGRAMS = dump_moo gragrep
NOINST_PROGRAMS_OPT = $(patsubst %,%.opt,$(EXTRA_PROGRAMS))

.PHONY: all
all: $(PROGRAMS) $(NOINST_PROGRAMS)

CMOS = $(ML:%.ml=%.cmo)
CCMOS = $(CML:%.ml=%.cmo)
MAINCMOS = $(MAINCML:%.ml=%.cmo)
CMXS = $(patsubst %.cmo,%.cmx,$(CMOS))
CCMXS = $(patsubst %.cmo,%.cmx,$(CCMOS))
MAINCMXS = $(patsubst %.cmo,%.cmx,$(MAINCMOS))
$(CMOS): $(LIB_DEPS)
$(CMXOS): $(LIBX_DEPS)
ifeq ($(MAKECMDGOALS),all)
   $(CMOS:%.cmo=%.cmi): $(LIB_DEPS)
endif
ifeq ($(MAKECMDGOALS),)
   $(CMOS:%.cmo=%.cmi): $(LIB_DEPS)
endif
ifeq ($(MAKECMDGOALS),opt)
   $(CMOS:%.cmo=%.cmi): $(LIBX_DEPS)
endif

LIB_DEPS := $(shell $(OCAMLFIND) query -recursive -predicates "byte" -format "%d/%a" $(MATITA_REQUIRES))
LIBX_DEPS := $(shell $(OCAMLFIND) query -recursive -predicates "native" -format "%d/%a" $(MATITA_REQUIRES))
CLIB_DEPS := $(shell $(OCAMLFIND) query -recursive -predicates "byte" -format "%d/%a" $(MATITA_CREQUIRES))
CLIBX_DEPS := $(shell $(OCAMLFIND) query -recursive -predicates "native" -format "%d/%a" $(MATITA_CREQUIRES))
opt: $(PROGRAMS_OPT) $(NOINST_PROGRAMS_OPT)
upx: $(PROGRAMS_UPX)
.PHONY: opt upx

ifeq ($(HAVE_OCAMLOPT),yes)
world: depend.opt opt links
else
world: depend all
endif

#links %.opt -> %
links:
	$(H)for X in $(INSTALL_PROGRAMS_LINKS_MATITAC) \
			$(INSTALL_PROGRAMS_LINKS_MATITA); do\
		ln -sf $$X.opt $$X;\
	done
	$(H)ln -sf matita.opt matita
	$(H)ln -sf matitac.opt matitac

linkonly:
	$(H)echo "  OCAMLC matita.ml"
	$(H)$(OCAMLC) $(PKGS) -linkpkg -o matita $(CMOS) matita.ml
	$(H)echo "  OCAMLC matitac.ml"
	$(H)$(OCAMLC) $(CPKGS) -linkpkg -o matitac $(CCMOS) $(MAINCMOS) matitac.ml
.PHONY: linkonly
matita: matita.ml $(LIB_DEPS) $(CMOS)
	$(H)echo "  OCAMLC $<"
	$(H)$(OCAMLC) $(PKGS) -linkpkg -o $@ $(CMOS) matita.ml
matita.opt: matita.ml $(LIBX_DEPS) $(CMXS)
	$(H)echo "  OCAMLOPT $<"
	$(H)$(OCAMLOPT) $(PKGS) -linkpkg -o $@ $(CMXS) matita.ml

dump_moo: dump_moo.ml buildTimeConf.cmo
	$(H)echo "  OCAMLC $<"
	$(H)$(OCAMLC) $(PKGS) -linkpkg -o $@ buildTimeConf.cmo $<
dump_moo.opt: dump_moo.ml buildTimeConf.cmx
	$(H)echo "OCAMLOPT $<"
	$(H)$(OCAMLOPT) $(PKGS) -linkpkg -o $@ buildTimeConf.cmx $<

matitac: matitac.ml $(CLIB_DEPS) $(CCMOS) $(MAINCMOS)
	$(H)echo "  OCAMLC $<"
	$(H)$(OCAMLC) $(CPKGS) -linkpkg -o $@ $(CCMOS) $(MAINCMOS) matitac.ml
matitac.opt: matitac.ml $(CLIBX_DEPS) $(CCMXS) $(MAINCMXS)
	$(H)echo "  OCAMLOPT $<"
	$(H)$(OCAMLOPT) $(CPKGS) -linkpkg -o $@ $(CCMXS) $(MAINCMXS) matitac.ml

matitatop: matitatop.ml $(CLIB_DEPS) $(CCMOS)
	$(H)echo "  OCAMLC $<"
	$(H)$(OCAMLC) $(CPKGS) -linkpkg -o $@ toplevellib.cma $(CCMOS) $<

matitaprover: matitac
	$(H)test -f $@ || ln -s $< $@
matitaprover.opt: matitac.opt
	$(H)test -f $@ || ln -s $< $@

matitadep: matitac
	$(H)test -f $@ || ln -s $< $@
matitadep.opt: matitac.opt
	$(H)test -f $@ || ln -s $< $@

matitawiki: matitac
	$(H)test -f $@ || ln -s $< $@
matitawiki.opt: matitac.opt
	$(H)test -f $@ || ln -s $< $@

matitaclean: matitac
	$(H)test -f $@ || ln -s $< $@
matitaclean.opt: matitac.opt
	$(H)test -f $@ || ln -s $< $@

matitamake: matitac
	$(H)test -f $@ || ln -s $< $@
matitamake.opt: matitac.opt
	$(H)test -f $@ || ln -s $< $@
	
gragrep: matitac
	$(H)test -f $@ || ln -s $< $@
gragrep.opt: matitac.opt
	$(H)test -f $@ || ln -s $< $@
	
cicbrowser: matita
	$(H)test -f $@ || ln -s $< $@
cicbrowser.opt: matita.opt
	$(H)test -f $@ || ln -s $< $@

matitaGeneratedGui.ml: matita.glade
	$(H)$(LABLGLADECC) -embed $< > matitaGeneratedGui.ml

.PHONY: clean
clean:
	$(H)rm -rf *.cma *.cmo *.cmi *.cmx *.cmxa *.a *.o \
		$(PROGRAMS) $(PROGRAMS_OPT) \
		$(NOINST_PROGRAMS) $(NOINST_PROGRAMS_OPT) \
		$(PROGRAMS_STATIC) \
		$(PROGRAMS_UPX) \
		*.stamp \
		$(NULL)

.PHONY: distclean
distclean: clean
	$(H)$(MAKE) -C dist/ clean
	$(H)rm -f matitaGeneratedGui.ml matitaGeneratedGui.mli
	$(H)rm -f buildTimeConf.ml
	$(H)rm -f matita.glade.bak matita.gladep.bak
	$(H)rm -f matita.conf.xml.sample
	$(H)rm -rf .matita

TEST_DIRS = 				\
	legacy                          \
	library 			\
	tests 				\
	dama				\
	contribs/CoRN	 	        \
	contribs/RELATIONAL	 	\
	contribs/LAMBDA-TYPES 		\
	contribs/PREDICATIVE-TOPOLOGY 	\
	$(NULL)

#	library_auto 			
TEST_DIRS_OPT = 			\
	$(TEST_DIRS)        \
	$(NULL)

.PHONY: tests tests.opt cleantests cleantests.opt
tests: $(foreach d,$(TEST_DIRS),$(d)-test)
tests.opt: $(foreach d,$(TEST_DIRS_OPT),$(d)-test-opt)
cleantests: $(foreach d,$(TEST_DIRS),$(d)-cleantests)
cleantests.opt: $(foreach d,$(TEST_DIRS_OPT),$(d)-cleantests-opt)

%-test: matitac matitadep matitaclean 
	-cd $* && make -k clean all
%-test-opt: matitac.opt matitadep.opt matitaclean.opt
	-cd $* && make -k clean.opt opt
%-cleantests: matitaclean
	-cd $* && make clean
%-cleantests-opt: matitaclean.opt
	-cd $* && make clean.opt

# {{{ Distribution stuff

ifeq ($(DISTRIBUTED),yes)


MATITA_CFLAGS = #-nodb

dist_library: install_preliminaries dist_library@standard-library
dist_library@%: 
	$(H)echo "MATITAMAKE init $*"
	$(H)(HOME=$(WHERE) USER=builder MATITA_RT_BASE_DIR=$(WHERE) MATITA_FLAGS='$(MATITA_CFLAGS)' $(WHERE)/matitamake init $* $(WHERE)/ma/$*)
	$(H)echo "MATITAMAKE publish $*"
	$(H)(HOME=$(WHERE) USER=builder MATITA_RT_BASE_DIR=$(WHERE) MATITA_FLAGS='$(MATITA_CFLAGS)' $(WHERE)/matitamake publish $*)
	$(H)echo "MATITAMAKE destroy $*"
	$(H)(HOME=$(WHERE) USER=builder MATITA_RT_BASE_DIR=$(WHERE) MATITA_FLAGS='$(MATITA_CFLAGS)' $(WHERE)/matitamake destroy $*)
	# sqlite3 only
	$(H)cp $(WHERE)/.matita/matita.db  $(WHERE)/metadata.db || true
	#$(H)rm -rf $(WHERE)/.matita/
	touch $@

endif

dist_pre: matitaGeneratedGui.ml
	$(MAKE) -C dist/ dist_pre

WHERE = $(DESTDIR)/$(RT_BASE_DIR)
INSTALL_STUFF = 			\
	icons/ 				\
	help/ 				\
	matita.gtkrc 			\
	matita.lang 			\
	matita.ma.templ 		\
	core_notation.moo 		\
	matita.conf.xml 		\
	closed.xml 			\
	gtkmathview.matita.conf.xml 	\
	template_makefile.in 		\
	AUTHORS 			\
	LICENSE 			\
	$(NULL)

ifeq ($(HAVE_OCAMLOPT),yes)
INSTALL_STUFF_BIN = $(INSTALL_PROGRAMS:%=%.opt) 
else
INSTALL_STUFF_BIN = $(INSTALL_PROGRAMS)
endif

install-arch: install_preliminaries 
install-indep: dist_library 

install_preliminaries : install_preliminaries.stamp

install_preliminaries.stamp:
	$(H)install -d $(WHERE)/ma/
	$(H)cp -a $(INSTALL_STUFF) $(WHERE)
ifeq ($(HAVE_OCAMLOPT),yes)
	$(H)install -s $(INSTALL_STUFF_BIN) $(WHERE)
	$(H)for p in $(INSTALL_PROGRAMS); do ln -fs $$p.opt $(WHERE)/$$p; done
else
	$(H)install $(INSTALL_STUFF_BIN) $(WHERE)
endif
	$(H)for p in $(INSTALL_PROGRAMS_LINKS_MATITAC); do \
		ln -fs matitac $(WHERE)/$$p;\
	done
	$(H)for p in $(INSTALL_PROGRAMS_LINKS_MATITA); do \
		ln -fs matita $(WHERE)/$$p;\
	done
	$(H)cp -a library/ $(WHERE)/ma/standard-library
	$(H)cp -a contribs/ $(WHERE)/ma/
	$(H)touch install_preliminaries.stamp

uninstall:
	$(H)rm -rf $(WHERE)

STATIC_LINK = dist/static_link/static_link
# for matita
STATIC_LIBS =	\
	t1 t1x	\
	gtkmathview_gmetadom mathview mathview_backend_gtk mathview_frontend_gmetadom \
	gtksourceview-1.0 \
	gdome gmetadom_gdome_cpp_smart \
	stdc++ \
	mysqlclient \
	expat \
	$(NULL)
STATIC_EXTRA_LIBS = -cclib -lt1x -cclib -lstdc++
# for matitac & co
STATIC_CLIBS = \
	gdome \
	mysqlclient \
	$(NULL)
STATIC_CLIBS_PROVER = \
        $(STATIC_CLIBS) \
	z \
	pcre \
	expat \
	xml2 \
	glib-2.0 \
	$(NULL)
STATIC_EXTRA_CLIBS =
PROGRAMS_STATIC = $(patsubst %,%.static,$(PROGRAMS_OPT))
PROGRAMS_UPX = $(patsubst %,%.upx,$(PROGRAMS_STATIC))

ifeq ($(HAVE_OCAMLOPT),yes)
static: $(STATIC_LINK) $(PROGRAMS_STATIC)
else
upx:
	$(H)echo "Native code compilation is disabled"
static:
	$(H)echo "Native code compilation is disabled"
endif

$(STATIC_LINK):
	$(MAKE) -C dist/ $(STATIC_LINK)

matita.opt.static: $(STATIC_LINK) $(LIBX_DEPS) $(CMXS) matita.ml
	$(STATIC_LINK) $(STATIC_LIBS) -- \
		$(OCAMLOPT) $(PKGS) -linkpkg -o $@ $(CMXS) matita.ml \
		$(STATIC_EXTRA_LIBS)
	strip $@
dump_moo.opt.static: $(STATIC_LINK) buildTimeConf.cmx dump_moo.ml
	$(STATIC_LINK) $(STATIC_CLIBS) -- \
		$(OCAMLOPT) $(PKGS) -linkpkg -o $@ $^ \
		$(STATIC_EXTRA_CLIBS)
	strip $@
matitac.opt.static: $(STATIC_LINK) $(CLIBX_DEPS) $(CCMXS) $(MAINCMXS) matitac.ml
	$(STATIC_LINK) $(STATIC_CLIBS) -- \
		$(OCAMLOPT) $(CPKGS) -linkpkg -o $@ $(CCMXS) $(MAINCMXS) matitac.ml \
		$(STATIC_EXTRA_CLIBS)
	strip $@
matitaprover.opt.static: $(STATIC_LINK) $(CLIBX_DEPS) $(CCMXS) $(MAINCMXS) matitac.ml
	$(STATIC_LINK) $(STATIC_CLIBS_PROVER) -- \
		$(OCAMLOPT) $(CPKGS) -linkpkg -o $@ $(CCMXS) $(MAINCMXS) matitac.ml \
		$(STATIC_EXTRA_CLIBS);
	strip $@
matitadep.opt.static: matitac.opt.static
	$(H)test -f $@ || ln -s $< $@
matitaclean.opt.static: matitac.opt.static
	$(H)test -f $@ || ln -s $< $@
matitawiki.opt.static: matitac.opt.static
	$(H)test -f $@ || ln -s $< $@
matitamake.opt.static: matitac.opt.static
	$(H)test -f $@ || ln -s $< $@
cicbrowser.opt.static: matita.opt.static
	$(H)test -f $@ || ln -s $< $@
cicbrowser.opt.static.upx: matita.opt.static.upx
	$(H)test -f $@ || ln -s $< $@

%.upx: %
	cp $< $@
	strip $@
	upx $@

# }}} End of distribution stuff

# {{{ Deps and automatic rules 
tags: TAGS
.PHONY: TAGS
TAGS:
	$(H)cd ..; otags -vi -r components/ matita/

.PHONY: depend
	
depend: 
	$(H)echo "  OCAMLDEP"
	$(H)$(OCAMLDEP) *.ml *.mli > .depend
depend.opt: 
	$(H)echo "  OCAMLDEP -native"
	$(H)$(OCAMLDEP) -native *.ml *.mli > .depend.opt

ifeq ($(MAKECMDGOALS),)
  include .depend   
endif

ifeq ($(MAKECMDGOALS), all)
  include .depend   
endif

ifeq ($(MAKECMDGOALS), opt)
  include .depend.opt   
endif

ifeq ($(MAKECMDGOALS), world)
  include .depend.opt   
endif

%.cmi: %.mli
	$(H)echo "  OCAMLC $<"
	$(H)$(OCAMLC) $(PKGS) -c $<
%.cmo %.cmi: %.ml
	$(H)echo "  OCAMLC $<"
	$(H)$(OCAMLC) $(PKGS) -c $<
%.cmx: %.ml
	$(H)echo "  OCAMLOPT $<"
	$(H)$(OCAMLOPT) $(PKGS) -c $<
%.annot: %.ml
	$(H)echo "  OCAMLC -dtypes $<"
	$(H)$(OCAMLC) -dtypes $(PKGS) -c $<

deps.ps: deps.dot
	dot -Tps -o $@ $<
deps.dot: .depend
	./dep2dot.rb < $< | tred > $@

# }}} End of deps and automatic rules

# vim: set foldmethod=marker:
