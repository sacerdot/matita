GOALS = all opt clean clean.opt

DEVELS = RELATIONAL LOGIC LAMBDA-TYPES assembly dama POPLmark CoRN character

$(GOALS): 
	@$(foreach DEVEL, $(DEVELS), $(MAKE) -C $(DEVEL) $@;) 

.PHONY: (GOALS)

.SUFFIXES:
