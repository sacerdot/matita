include ../Makefile.defs

H=@

MATITAOPTIONS=$(MATITAUSEROPTIONS) -onepass

DIR=$(shell basename $$PWD)

MMAS = $(shell find Legacy-2 -name "*.mma")
# Base-2 
MAS = $(MMAS:%.mma=%.ma)
XMAS = Legacy-2/theory.ma Base-2/theory.ma LambdaDelta-2/theory.ma

$(DIR) all: depends
	$(H)$(MAKE) H=$(H) --no-print-directory build

$(DIR).opt opt all.opt: depends
	$(H)$(MAKE) H=$(H) --no-print-directory build.opt

build: $(MAS)
	$(H)echo Legacy-2/theory.ma `$(BIN)matitadep.opt -stdout Legacy-2/theory.ma` >> depends
#	$(H)echo Base-2/theory.ma `$(BIN)matitadep.opt -stdout Base-2/theory.ma` >> depends
	$(H)$(BIN)matitac $(MATITAOPTIONS) 2> /dev/null
	$(H)rm depends

build.opt: $(MAS)
	$(H)echo Legacy-2/theory.ma `$(BIN)matitadep.opt -stdout Legacy-2/theory.ma` >> depends
#	$(H)echo Base-2/theory.ma `$(BIN)matitadep.opt -stdout Base-2/theory.ma` >> depends
	$(H)$(BIN)matitac.opt $(MATITAOPTIONS) 2> /dev/null
	$(H)rm depends

clean:
	$(H)$(BIN)matitaclean $(MATITAOPTIONS)
	$(H)rm -f $(MAS) depends

clean.opt:
	$(H)$(BIN)matitaclean.opt $(MATITAOPTIONS)
	$(H)rm -f $(MAS) depends

clean.ma:
	$(H)$(BIN)matitaclean.opt $(MATITAOPTIONS) $(MAS)
	$(H)rm -f $(MAS) depends

depend:
	@echo matitadep
	$(H)$(BIN)matitadep $(foreach FILE,$(XMAS),-exclude $(FILE))
	$(H)cat Legacy-2/depends >> depends
# Base-2/depends
	
depend.opt:
	@echo matitadep.opt
	$(H)$(BIN)matitadep.opt $(foreach FILE,$(XMAS),-exclude $(FILE))
	$(H)cat Legacy-2/depends >> depends
# Base-2/depends

depends: depend.opt

%.ma: %.mma
	$(H)$(BIN)matitac.opt $(MATITAOPTIONS) $(word 3,$(shell grep -h $< */depends)) `$(BIN)matitadep.opt -stdout $<` 2> /dev/null
	$(H)$(BIN)matitac.opt $(MATITAOPTIONS) -dump $@ $< 2> /dev/null
	$(H)echo $@ `$(BIN)matitadep.opt -stdout $@` >> depends

include Legacy-2/.depend
# include Base-2/.depend
