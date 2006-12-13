GOALS = all opt clean clean.opt

DEVELS = ../library RELATIONAL LAMBDA-TYPES

$(GOALS): 
	@$(foreach DEVEL, $(DEVELS), $(MAKE) -C $(DEVEL) $@;) 

.PHONY: (GOALS)

.SUFFIXES:
