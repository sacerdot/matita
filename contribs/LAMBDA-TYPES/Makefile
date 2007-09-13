GOALS = all opt clean clean.opt

DEVELS = Base-2 Unified-Sub 

$(GOALS): 
	@$(foreach DEVEL, $(DEVELS), $(MAKE) -k -C $(DEVEL) $@;) 

.PHONY: (GOALS)

.SUFFIXES:
