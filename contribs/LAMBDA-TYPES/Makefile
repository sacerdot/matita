GOALS = all opt clean clean.opt

DEVELS = Base-1 LambdaDelta-1 Unified

$(GOALS): 
	@$(foreach DEVEL, $(DEVELS), $(MAKE) -C $(DEVEL) $@;) 

.PHONY: (GOALS)

.SUFFIXES:
