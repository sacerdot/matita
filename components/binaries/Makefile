H=@

#FG matex renders lamdba-terms to LaTeX
#FG matitadep exports the dependencies of .ma files
#FG probe returns statistics on compiled files
#FG xoa generates matita files for n-ary logical operators/quantifiers
BINARIES=matex matitadep probe xoa

all: $(BINARIES:%=rec@all@%) 
opt: $(BINARIES:%=rec@opt@%)
depend: $(BINARIES:%=rec@depend@%)
depend.opt: $(BINARIES:%=rec@depend.opt@%)
install: $(BINARIES:%=rec@install@%)
uninstall: $(BINARIES:%=rec@uninstall@%)
clean: $(BINARIES:%=rec@clean@%) 

rec@%:
	$(H)$(MAKE) -C $(word 2, $(subst @, ,$*)) $(word 1, $(subst @, ,$*))

