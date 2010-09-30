GOALS = all opt clean clean.opt

DEVELS = dama dama_didactic dama_duality

$(GOALS): 
	@$(foreach DEVEL, $(DEVELS), $(MAKE) -C $(DEVEL) $@;) 

.PHONY: (GOALS)

.SUFFIXES:
