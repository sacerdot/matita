GOALS = all opt clean clean.opt

DEVELS = Base-1 LambdaDelta-1 Base-2 Unified-Sub 

$(GOALS): 
	@$(foreach DEVEL, $(DEVELS), $(MAKE) -k -C $(DEVEL) $@;) 

.PHONY: (GOALS)

.SUFFIXES:
