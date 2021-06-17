H=@

BINARIES = inline xhtbl index roles recomm

all: $(BINARIES:%=rec@all@%)
clean: $(BINARIES:%=rec@clean@%) 

rec@%:
	$(H)$(MAKE) -C $(word 2, $(subst @, ,$*)) $(word 1, $(subst @, ,$*))

