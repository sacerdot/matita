DIR=$(shell basename $$PWD)

MMAS = $(shell find -name "*.mma")
MAS = $(MMAS:%.mma=%.ma)

%.ma: %.mma
	echo -e "$< preamble.ma \npreamble.ma" > depends
	../../../matitac.opt -dump $@ $< 2>/dev/null
	../../../matitadep.opt
	../../../matitac.opt $@

$(DIR) all: $(MAS)
	../../../matitac
$(DIR).opt opt all.opt: $(MAS)
	../../../matitac.opt
clean:
	../../../matitaclean
	rm -f $(MAS)
clean.opt:
	../../../matitaclean.opt
	rm -f $(MAS)

theory2.ma: theory2.mma ext/tactics2.ma ext/arith2.ma types/props2.ma blt/props2.ma plist/props2.ma 
types/props2.ma: types/props2.mma types/defs2.ma 
blt/props2.ma: blt/props2.mma blt/defs2.ma 
plist/props2.ma: plist/props2.mma plist/defs2.ma 
