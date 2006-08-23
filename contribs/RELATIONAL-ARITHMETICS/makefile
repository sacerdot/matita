H=@

RT_BASEDIR=/home/fguidi/svn/software/matita/
OPTIONS=-bench
MMAKE=$(RT_BASEDIR)matitamake $(OPTIONS)
CLEAN=$(RT_BASEDIR)matitaclean $(OPTIONS) 
MMAKEO=$(RT_BASEDIR)matitamake.opt $(OPTIONS)
CLEANO=$(RT_BASEDIR)matitaclean.opt $(OPTIONS) 

devel:=$(shell basename `pwd`)

all: preall
	$(H)MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKE) build $(devel)
clean: preall
	$(H)MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKE) clean $(devel)
cleanall: preall
	$(H)MATITA_FLAGS=$(MATITA_FLAGS) $(MCLEAN) all

all.opt opt: preall
	$(H)MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKEO) build $(devel)
clean.opt: preall
	$(H)MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKEO) clean $(devel)
cleanall.opt: preall
	$(H)MATITA_FLAGS=$(MATITA_FLAGS) $(MCLEANO) all

%.mo: preall
	$(H)MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKE) $@
%.mo.opt: preall
	$(H)MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKEO) $@
	
preall:
	$(H)MATITA_FLAGS=$(MATITA_FLAGS) $(MMAKE) init $(devel)

