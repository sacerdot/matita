GOALS = all opt clean clean.opt

DEVELS = RELATIONAL LOGIC LAMBDA-TYPES assembly dama

$(GOALS): 
	@$(foreach DEVEL, $(DEVELS), $(MAKE) -C $(DEVEL) $@;) 

.PHONY: (GOALS)

.SUFFIXES:
