GOALS = all opt clean clean.opt

DEVELS = ../library ../legacy RELATIONAL LOGIC LAMBDA-TYPES

$(GOALS): 
	@$(foreach DEVEL, $(DEVELS), $(MAKE) -C $(DEVEL) $@;) 

.PHONY: (GOALS)

.SUFFIXES:
