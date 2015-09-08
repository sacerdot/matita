include ../Makefile.defs

DIR=$(shell basename $$PWD)

H=@

MATITAOPTIONS=$(MATITAUSEROPTIONS) -onepass

LOG = log.txt

MMAS = $(shell find -name "*.mma")
MAS = $(MMAS:%.mma=%.ma)

$(DIR) all:
	$(H)$(RM) $(LOG)
	$(H)$(BIN)matitac $(MATITAOPTIONS) 2>> $(LOG)
$(DIR).opt opt all.opt:
	$(H)$(RM) $(LOG)
	$(H)$(BIN)matitac.opt $(MATITAOPTIONS) 2>> $(LOG)

%.ma %.mma: 
	$(H)$(RM) $(LOG)
	$(H)$(BIN)matitac $(MATITAOPTIONS) $@ 2>> $(LOG)
%.ma.opt: 
	$(H)$(RM) $(LOG)
	$(H)$(BIN)matitac.opt $(MATITAOPTIONS) $*.ma 2>> $(LOG)
%.mma.opt: 
	$(H)$(RM) $(LOG)
	$(H)$(BIN)matitac.opt $(MATITAOPTIONS) $*.mma 2>> $(LOG)

clean:
	$(H)$(BIN)matitaclean $(MATITAOPTIONS)
	$(H)$(RM) $(MAS)
clean.opt:
	$(H)$(BIN)matitaclean.opt $(MATITAOPTIONS)
	$(H)$(RM) $(MAS)

depend:
	$$(H)(BIN)matitadep $(MATITAOPTIONS)
depend.opt:
	$(H)$(BIN)matitadep.opt $(MATITAOPTIONS)

ifneq ($(strip $(MAS)),)
clean.ma:
	$(H)$(BIN)matitaclean.opt $(MATITAOPTIONS) $(MAS)
	$(H)$(RM) $(MAS)
else
clean.ma:
	$(H)echo no files to clean
endif
