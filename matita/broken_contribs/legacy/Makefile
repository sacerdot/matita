DIR=$(shell basename $$PWD)
MATITAOPTIONS=-onepass

$(DIR) all:
	../matitac $(MATITAOPTIONS)
$(DIR).opt opt all.opt:
	../matitac.opt $(MATITAOPTIONS)
clean:
	../matitaclean $(MATITAOPTIONS)
clean.opt:
	../matitaclean.opt $(MATITAOPTIONS)
depend:
	../matitadep
depend.opt:
	../matitadep.opt
