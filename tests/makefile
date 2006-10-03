H=@

RT_BASEDIR=../
OPTIONS=-bench
MMAKE=$(RT_BASEDIR)matitamake $(OPTIONS)
CLEAN=$(RT_BASEDIR)matitaclean $(OPTIONS) 
MMAKEO=$(RT_BASEDIR)matitamake.opt $(OPTIONS)
CLEANO=$(RT_BASEDIR)matitaclean.opt $(OPTIONS) 

devel:=$(shell basename `pwd`)

ifneq "$(SRC)" ""
  XXX=SRC=$(SRC)
endif

all: preall
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKE) build $(devel)
clean: preall
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKE) clean $(devel)
cleanall: preall
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MCLEAN) all

all.opt opt: preall
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKEO) build $(devel)
clean.opt: preall
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKEO) clean $(devel)
cleanall.opt: preall
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MCLEANO) all

%.mo: preall
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKE) $@
%.mo.opt: preall
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKEO) $@
	
preall:
	$(H)$(XXX) MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKE) init $(devel)

