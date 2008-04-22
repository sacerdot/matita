GOALS = all opt clean clean.opt

DEVELS = dama dama_didactic

$(GOALS): 
	@$(foreach DEVEL, $(DEVELS), $(MAKE) -C $(DEVEL) $@;) 

.PHONY: (GOALS)

.SUFFIXES:
