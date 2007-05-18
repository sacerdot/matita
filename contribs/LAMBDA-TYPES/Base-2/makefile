H=@

RT_BASEDIR=/home/fguidi/svn/software/matita/
OPTIONS=-bench
MMAKE=$(RT_BASEDIR)matitamake $(OPTIONS)
CLEAN=$(RT_BASEDIR)matitaclean $(OPTIONS) 
MMAKEO=$(RT_BASEDIR)matitamake.opt $(OPTIONS)
CLEANO=$(RT_BASEDIR)matitaclean.opt $(OPTIONS) 

devel:=$(shell basename `pwd`)

ifneq "$(SRC)" ""
  XXX="SRC=$(SRC)"
endif

all: build_mas preall 
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKE) build $(devel)
clean: clean_mas preall
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKE) clean $(devel)
cleanall: clean_mas preall
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MCLEAN) all

all.opt opt: build_mas preall.opt
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKEO) build $(devel)
clean.opt: clean_mas preall.opt
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKEO) clean $(devel)
cleanall.opt: clean_mas preall.opt
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MCLEANO) all

%.mo: preall
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKE) $@
%.mo.opt: preall.opt
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKEO) $(@:.opt=)
	
preall:
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKE) init $(devel)

preall.opt:
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKEO) init $(devel)


# FG: added part ############################################################

build_mas:
	$(H)$(MAKE) preamble.mo.opt
	$(H)$(MAKE) -f Makefile
	$(H)$(MAKE) preall.opt
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKEO) clean $(devel)

clean_mas:
	$(H)$(MAKE) -f Makefile clean
