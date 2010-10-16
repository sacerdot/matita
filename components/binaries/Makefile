H=@

#CSC: saturate is broken after the huge refactoring of auto/paramodulation
#CSC: by Andrea
#BINARIES=extractor  table_creator  utilities saturate
#BINARIES=transcript

all: $(BINARIES:%=rec@all@%) 
opt: $(BINARIES:%=rec@opt@%)
depend: $(BINARIES:%=rec@depend@%)
depend.opt: $(BINARIES:%=rec@depend.opt@%)
install: $(BINARIES:%=rec@install@%)
uninstall: $(BINARIES:%=rec@uninstall@%)
clean: $(BINARIES:%=rec@clean@%) 

rec@%:
	$(H)$(MAKE) -C $(word 2, $(subst @, ,$*)) $(word 1, $(subst @, ,$*))

