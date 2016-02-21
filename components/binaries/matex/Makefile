EXEC = matex
VERSION=0.1.0

REQUIRES = helm-ng_library

include ../Makefile.common

PROBE    = ../probe/probe.native
REGISTRY = $(RT_BASE_DIR)/matita.conf.xml
OBJS     = Make.objs

BASEURI = cic:/matita/lambdadelta/basic_1/

test: test/$(OBJS)

$(OBJS):
	@echo probe: $(BASEURI)
	$(H)$(PROBE) $(REGISTRY) -g $(BASEURI) -os > $@

test/$(OBJS): $(OBJS) ./matex.native
	@echo MaTeX: processing $(OBJS)
	$(H)./matex.native -O test -l $(OBJS) -t -p $(REGISTRY) `cat $<`

.PHONY: test
