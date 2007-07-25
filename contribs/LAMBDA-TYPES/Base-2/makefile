H=@

RT_BASEDIR=../../../
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

mas: preall
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKE) build $(devel)
mas.opt: preall.opt
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKEO) build $(devel)

%.mo: preall
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKE) $@
%.mo.opt: preall.opt
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKEO) $(@:.opt=)
	
preall:
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKE) init $(devel)

preall.opt:
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKEO) init $(devel)

# FG: added part ############################################################

MATITAC = $(RT_BASEDIR)/matitac.opt

MMAS = $(shell find -name "*.mma")
MAS = $(MMAS:%.mma=%.ma)

build_mas: preall.opt theory.ma

clean_mas:
	$(H)rm -f $(MAS)

%.ma: %.mma
	$(H)$(MATITAC) -dump $@ $< $(OPTIONS)
	$(MAKE) preall.opt

include depend

.DELETE_ON_ERROR:
