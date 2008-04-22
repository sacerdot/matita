SRC=$(wildcard *.ma)

MATITA_FLAGS = -I ../..
NODB=false
ifeq ($(NODB),true)
	MATITA_FLAGS += -nodb
endif

MATITAC=../../scripts/do_tests.sh $(DO_TESTS_OPTS) "../../matitac $(MATITA_FLAGS) -noprofile" "../../matitaclean $(MATITA_FLAGS)" /dev/null FAIL
MATITACOPT=../../scripts/do_tests.sh $(DO_TESTS_OPTS) "../../matitac.opt $(MATITA_FLAGS) -noprofile" "../../matitaclean.opt $(MATITA_FLAGS)" /dev/null FAIL
VERBOSEMATITAC=../../matitac $(MATITA_FLAGS)
VERBOSEMATITACOPT=../../matitac.opt $(MATITA_FLAGS)

MATITACLEAN=../../matitaclean $(MATITA_FLAGS)
MATITACLEANOPT=../../matitaclean.opt $(MATITA_FLAGS)

MATITADEP=../../matitadep $(MATITA_FLAGS)
MATITADEPOPT=../../matitadep.opt $(MATITA_FLAGS)

DEPEND_NAME=.depend

H=@

all: $(SRC:%.ma=%.mo)

opt:
	$(H)$(MAKE) MATITAC='$(MATITACOPT)' MATITACLEAN='$(MATITACLEANOPT)' MATITADEP='$(MATITADEPOPT)' all

verbose:
	$(H)$(MAKE) MATITAC='$(VERBOSEMATITAC)' MATITACLEAN='$(MATITACLEAN)' MATITADEP='$(MATITADEP)' all

%.opt:
	$(H)$(MAKE) MATITAC='$(MATITACOPT)' MATITACLEAN='$(MATITACLEANOPT)' MATITADEP='$(MATITADEPOPT)' $(@:%.opt=%)

clean_:
	$(H)rm -f __*not_for_matita

clean: clean_
	$(H)$(MATITACLEAN) $(SRC)

cleanall: clean_
	$(H)rm -f $(SRC:%.ma=%.moo)
	$(H)$(MATITACLEAN) all

depend:
	$(H)rm -f $(DEPEND_NAME)
	$(H)$(MAKE) $(DEPEND_NAME)
.PHONY: depend

%.moo:
	$(H)$(MATITAC) $<

$(DEPEND_NAME): $(SRC)
	$(H)$(MATITADEP) $(SRC) > $@ || rm -f $@

#include $(DEPEND_NAME)
include .depend
