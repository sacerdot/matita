EXEC = matex
VERSION=0.1.0

REQUIRES = helm-ng_library

include ../Makefile.common

PROBE    = ../probe/probe.native
REGISTRY = $(RT_BASE_DIR)/matita.conf.xml \
           test/legacy_1.conf.xml test/ground_1.conf.xml test/basic_1.conf.xml
OBJS     = Make.objs
SRCS     = Make.srcs

DEVEL = ../../../matita/contribs/lambdadelta/basic_1/

test: test/$(SRCS)

test/$(OBJS): $(REGISTRY)
	@echo probe: $(DEVEL)
	$(H)$(PROBE) $(REGISTRY) -g $(DEVEL) -os > $@

test/$(SRCS): test/$(OBJS) $(REGISTRY) ./matex.native
	@echo MaTeX: processing $<
	$(H)./matex.native -O test -l $(SRCS) -p -g -a $(REGISTRY) `cat $<`

.PHONY: test
