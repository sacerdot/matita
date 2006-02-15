export SHELL=/bin/bash

include ../Makefile.defs

NULL =
H=@

OCAML_FLAGS = -pp $(CAMLP4O)
PKGS = -package "$(MATITA_REQUIRES)"
CPKGS = -package "$(MATITA_CREQUIRES)"
OCAML_THREADS_FLAGS = -thread
OCAML_DEBUG_FLAGS = -g
OCAMLC_FLAGS = $(OCAML_FLAGS) $(OCAML_THREADS_FLAGS)
OCAMLC = $(OCAMLFIND) ocamlc $(OCAMLC_FLAGS) $(OCAML_DEBUG_FLAGS)
OCAMLOPT = $(OCAMLFIND) opt $(OCAMLC_FLAGS)
OCAMLDEP = $(OCAMLFIND) ocamldep $(OCAML_FLAGS)

MATITA_FLAGS = -noprofile
NODB=false
ifeq ($(NODB),true)
	MATITA_FLAGS += -nodb
endif

# objects for matita (GTK GUI)
CMOS =				\
	buildTimeConf.cmo	\
	matitaTypes.cmo		\
	matitaMisc.cmo		\
	matitamakeLib.cmo	\
	matitaInit.cmo		\
	matitaExcPp.cmo 	\
	matitaEngine.cmo	\
	matitacLib.cmo		\
	matitaScript.cmo	\
	matitaGeneratedGui.cmo	\
	matitaGtkMisc.cmo	\
	applyTransformation.cmo	\
	matitaMathView.cmo 	\
	matitaGui.cmo		\
	$(NULL)
# objects for matitac (batch compiler)
CCMOS =				\
	buildTimeConf.cmo	\
	matitaTypes.cmo		\
	matitaMisc.cmo		\
	matitamakeLib.cmo	\
	matitaInit.cmo		\
	matitaExcPp.cmo 	\
	matitaEngine.cmo	\
	matitacLib.cmo		\
	$(NULL)
MAINCMOS =			\
	matitadep.cmo		\
	matitaclean.cmo		\
	matitamake.cmo		\
	$(NULL)
PROGRAMS_BYTE = matita matitac cicbrowser matitadep matitaclean matitamake dump_moo
PROGRAMS = $(PROGRAMS_BYTE) matitatop
PROGRAMS_OPT = $(patsubst %,%.opt,$(PROGRAMS_BYTE))

.PHONY: all
all: $(PROGRAMS)
#  all: matita.conf.xml $(PROGRAMS) coq.moo

#  matita.conf.xml: matita.conf.xml.sample
#          @if diff matita.conf.xml.sample matita.conf.xml 1>/dev/null 2>/dev/null; then\
#                  touch matita.conf.xml;\
#          else\
#                  echo;\
#                  echo "matita.conf.xml.sample is newer than matita.conf.xml";\
#                  echo;\
#                  echo "PLEASE update your configuration file!";\
#                  echo "(copying matita.conf.xml.sample should work)";\
#                  echo;\
#                  false;\
#          fi

#  coq.moo: library/legacy/coq.ma matitac
#          ./matitac $(MATITA_FLAGS) $<
#  coq.moo.opt: library/legacy/coq.ma matitac.opt
#          ./matitac.opt $(MATITA_FLAGS) $<

CMXS = $(patsubst %.cmo,%.cmx,$(CMOS))
CCMXS = $(patsubst %.cmo,%.cmx,$(CCMOS))
MAINCMXS = $(patsubst %.cmo,%.cmx,$(MAINCMOS))
LIB_DEPS := $(shell $(OCAMLFIND) query -recursive -predicates "byte" -format "%d/%a" $(MATITA_REQUIRES))
LIBX_DEPS := $(shell $(OCAMLFIND) query -recursive -predicates "native" -format "%d/%a" $(MATITA_REQUIRES))
CLIB_DEPS := $(shell $(OCAMLFIND) query -recursive -predicates "byte" -format "%d/%a" $(MATITA_CREQUIRES))
CLIBX_DEPS := $(shell $(OCAMLFIND) query -recursive -predicates "native" -format "%d/%a" $(MATITA_CREQUIRES))
opt: $(PROGRAMS_OPT)
upx: $(PROGRAMS_UPX)
.PHONY: opt upx

ifeq ($(HAVE_OCAMLOPT),yes)
world: all opt
else
world: all
endif

matita: matita.ml $(LIB_DEPS) $(CMOS)
	@echo "OCAMLC $<"
	$(H)$(OCAMLC) $(PKGS) -linkpkg -o $@ $(CMOS) matita.ml
matita.opt: matita.ml $(LIBX_DEPS) $(CMXS)
	@echo "OCAMLOPT $<"
	$(H)$(OCAMLOPT) $(PKGS) -linkpkg -o $@ $(CMXS) matita.ml

dump_moo: dump_moo.ml buildTimeConf.cmo
	@echo "OCAMLC $<"
	$(H)$(OCAMLC) $(PKGS) -linkpkg -o $@ buildTimeConf.cmo $<
dump_moo.opt: dump_moo.ml buildTimeConf.cmx
	@echo "OCAMLOPT $<"
	$(H)$(OCAMLOPT) $(PKGS) -linkpkg -o $@ buildTimeConf.cmx $<

matitac: matitac.ml $(CLIB_DEPS) $(CCMOS) $(MAINCMOS)
	@echo "OCAMLC $<"
	$(H)$(OCAMLC) $(CPKGS) -linkpkg -o $@ $(CCMOS) $(MAINCMOS) matitac.ml
matitac.opt: matitac.ml $(CLIBX_DEPS) $(CCMXS) $(MAINCMXS)
	@echo "OCAMLOPT $<"
	$(H)$(OCAMLOPT) $(CPKGS) -linkpkg -o $@ $(CCMXS) $(MAINCMXS) matitac.ml

matitatop: matitatop.ml $(CLIB_DEPS) $(CCMOS)
	@echo "OCAMLC $<"
	$(H)$(OCAMLC) $(CPKGS) -linkpkg -o $@ toplevellib.cma $(CCMOS) $<

matitadep: matitac
	@test -f $@ || ln -s $< $@
matitadep.opt: matitac.opt
	@test -f $@ || ln -s $< $@

matitaclean: matitac
	@test -f $@ || ln -s $< $@
matitaclean.opt: matitac.opt
	@test -f $@ || ln -s $< $@

matitamake: matitac
	@test -f $@ || ln -s $< $@
matitamake.opt: matitac.opt
	@test -f $@ || ln -s $< $@
	
cicbrowser: matita
	@test -f $@ || ln -s $< $@
cicbrowser.opt: matita.opt
	@test -f $@ || ln -s $< $@

matitaGeneratedGui.ml matitaGeneratedGui.mli: matita.glade
	$(LABLGLADECC) -embed $< > matitaGeneratedGui.ml
	$(OCAMLC) $(PKGS) -i matitaGeneratedGui.ml > matitaGeneratedGui.mli

.PHONY: clean
clean:
	rm -rf *.cma *.cmo *.cmi *.cmx *.cmxa *.a *.o \
		$(PROGRAMS) \
		$(PROGRAMS_OPT) \
		$(PROGRAMS_STATIC) \
		$(PROGRAMS_UPX) \
		$(NULL)

.PHONY: distclean
distclean: clean
	$(MAKE) -C dist/ clean
	rm -f matitaGeneratedGui.ml matitaGeneratedGui.mli
	rm -f buildTimeConf.ml
	rm -f matita.glade.bak matita.gladep.bak
	rm -f matita.conf.xml.sample
	rm -rf .matita

TEST_DIRS = 				\
	library 			\
	tests 				\
	tests/bad_tests 		\
	contribs/LAMBDA-TYPES 		\
	contribs/PREDICATIVE-TOPOLOGY 	\
	$(NULL)

.PHONY: tests tests.opt cleantests cleantests.opt
tests: $(foreach d,$(TEST_DIRS),$(d)-test)
tests.opt: $(foreach d,$(TEST_DIRS),$(d)-test-opt)
cleantests: $(foreach d,$(TEST_DIRS),$(d)-cleantests)
cleantests.opt: $(foreach d,$(TEST_DIRS),$(d)-cleantests-opt)

%-test: matitac matitadep matitaclean 
	-cd $* && make -k clean all
%-test-opt: matitac.opt matitadep.opt matitaclean.opt
	-cd $* && make -k clean.opt opt
%-cleantests: matitaclean
	-cd $* && make clean
%-cleantests-opt: matitaclean.opt
	-cd $* && make clean.opt

# {{{ Distribution stuff

ifeq ($(HAVE_OCAMLOPT),yes)
BEST=opt
BEST_EXT=.opt
else
BEST=all
BEST_EXT=
endif

ifeq ($(DISTRIBUTED),yes)

dist_library: dist_library@library
dist_library_clean:
	@echo "MATITACLEAN -system all"
	$(H)./matitaclean$(BEST_EXT) \
		-system -conffile `pwd`/matita.conf.xml.build all
dist_library@%:
	@echo "MATITAMAKE -system init"
	$(H)MATITA_RT_BASE_DIR=`pwd` \
		MATITA_FLAGS="-system -conffile `pwd`/matita.conf.xml.build" \
		./matitamake$(BEST_EXT) -conffile `pwd`/matita.conf.xml.build \
			init $* `pwd`/$*
	@echo "MATITAMAKE -system build"
	$(H)MATITA_RT_BASE_DIR=`pwd` \
		MATITA_FLAGS="-system -conffile `pwd`/matita.conf.xml.build" \
		./matitamake$(BEST_EXT) -conffile `pwd`/matita.conf.xml.build \
			build $*
	touch $@

endif

DESTDIR = $(RT_BASE_DIR)
INSTALL_STUFF = 			\
	icons/ 				\
	matita.gtkrc 			\
	matita.lang 			\
	matita.ma.templ 		\
	core_notation.moo 		\
	matita.conf.xml 		\
	matita.conf.xml.user 		\
	closed.xml 			\
	gtkmathview.matita.conf.xml 	\
	template_makefile.in 		\
	AUTHORS 			\
	LICENSE 			\
	$(NULL)
ifeq ($(HAVE_OCAMLOPT),yes)
INSTALL_STUFF += $(PROGRAMS_OPT)
else
INSTALL_STUFF += $(PROGRAMS_BYTE)
endif

install:
	# install main dir and executables
	install -d $(DESTDIR)
	cp -a $(INSTALL_STUFF) $(DESTDIR)
	# install the library and corresponding scripts
	if [ -d $(DESTDIR)/library ]; then rm -rf $(DESTDIR)/library; fi
	cp -a .matita/xml/matita/ $(DESTDIR)/library/
	if [ -d $(DESTDIR)/ma ]; then rm -rf $(DESTDIR)/ma; fi
	install -d $(DESTDIR)/ma
ifeq ($(HAVE_OCAMLOPT),yes)
	for p in $(PROGRAMS_BYTE); do ln -s $$p.opt $(DESTDIR)/$$p; done
endif
	cp -a library/ $(DESTDIR)/ma/stdlib/
	cp -a contribs/ $(DESTDIR)/ma/contribs/
uninstall:
	rm -rf $(DESTDIR)

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
STATIC_EXTRA_CLIBS =
PROGRAMS_STATIC = $(patsubst %,%.static,$(PROGRAMS_OPT))
PROGRAMS_UPX = $(patsubst %,%.upx,$(PROGRAMS_STATIC))

ifeq ($(HAVE_OCAMLOPT),yes)
static: $(STATIC_LINK) $(PROGRAMS_STATIC)
else
upx:
	@echo "Native code compilation is disabled"
static:
	@echo "Native code compilation is disabled"
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
matitadep.opt.static: matitac.opt.static
	@test -f $@ || ln -s $< $@
matitaclean.opt.static: matitac.opt.static
	@test -f $@ || ln -s $< $@
matitamake.opt.static: matitac.opt.static
	@test -f $@ || ln -s $< $@
cicbrowser.opt.static: matita.opt.static
	@test -f $@ || ln -s $< $@
cicbrowser.opt.static.upx: matita.opt.static.upx
	@test -f $@ || ln -s $< $@

%.upx: %
	cp $< $@
	strip $@
	upx $@

# }}} End of distribution stuff

tags: TAGS
.PHONY: TAGS
TAGS:
	cd ..; otags -vi -r components/ matita/

#.depend: matitaGeneratedGui.ml matitaGeneratedGui.mli *.ml *.mli

.PHONY: depend
depend:
	$(OCAMLDEP) *.ml *.mli > .depend

include .depend

%.cmi: %.mli
	@echo "OCAMLC $<"
	$(H)$(OCAMLC) $(PKGS) -c $<
%.cmo %.cmi: %.ml
	@echo "OCAMLC $<"
	$(H)$(OCAMLC) $(PKGS) -c $<
%.cmx: %.ml
	@echo "OCAMLOPT $<"
	$(H)$(OCAMLOPT) $(PKGS) -c $<
%.annot: %.ml
	@echo "OCAMLC -dtypes $<"
	$(H)$(OCAMLC) -dtypes $(PKGS) -c $<

$(CMOS): $(LIB_DEPS)
$(CMOS:%.cmo=%.cmx): $(LIBX_DEPS)

ifeq ($(MAKECMDGOALS),all)
   $(CMOS:%.cmo=%.cmi): $(LIB_DEPS)
endif
ifeq ($(MAKECMDGOALS),)
   $(CMOS:%.cmo=%.cmi): $(LIB_DEPS)
endif
ifeq ($(MAKECMDGOALS),opt)
   $(CMOS:%.cmo=%.cmi): $(LIBX_DEPS)
endif

# vim: set foldmethod=marker:
