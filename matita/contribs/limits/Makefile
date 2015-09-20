H    := @

ALPHA_DIR ?= $(HOME)/mps/ocamlbuild/alpha
ALPHA      = alpha.native

MATITAC = ../../matitac.opt

PRB_DIR      := ../../../components/binaries/probe
PRB          := probe.native
PRB_OPTS     := ../../matita.conf.xml -g -i

AMAS = $(wildcard *.ama)

all: $(AMAS:%.ama=%.ma)
	@$(MATITAC)

clean:
	$(H)$(RM) *~

clean_all: clean
	$(H)$(RM) $(AMAS:%.ama=%.ma)

probe:
	@echo PROBE .
	$(H)$(PRB_DIR)/$(PRB) $(PRB_OPTS) .

.PHONY: all clean clean_all probe

%.ma: %.ama
	$(H)$(ALPHA_DIR)/$(ALPHA) < $< > $@ 
