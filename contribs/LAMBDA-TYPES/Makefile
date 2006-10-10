GOALS = all opt clean clean.opt

DEVELS = Level-1/Base Level-1/LambdaDelta Unified

$(GOALS): 
	@$(foreach DEVEL, $(DEVELS), $(MAKE) -C $(DEVEL) $@;) 

.PHONY: (GOALS)

.SUFFIXES:
