DIR=$(shell basename $$PWD)

$(DIR) all:
	../matitac
$(DIR).opt opt all.opt:
	../matitac.opt
clean:
	../matitaclean
clean.opt:
	../matitaclean.opt
depend:
	../matitadep -dot
depend.opt:
	../matitadep.opt -dot

%.mo: 
	../matitac $*.ma
%.mo.opt: 
	../matitac.opt $*.ma
