include ../../../../Makefile.defs

H=@

MATITAC = $(RT_BASE_DIR)/matitac.opt

MMAS = $(shell find -name "*.mma")
MAS = $(MMAS:%.mma=%.ma)

all: OPTIONS = -bench

log: OPTIONS = >> tmp.txt 2>&1 
 
all: $(MAS)

log: $(MAS)
	$(H)mv tmp.txt log.txt

clean:
	$(H)rm -f $(MAS)

%.ma: %.mma
	$(H)$(MATITAC) -dump $@ $< $(OPTIONS)  

include depend

.DELETE_ON_ERROR:
