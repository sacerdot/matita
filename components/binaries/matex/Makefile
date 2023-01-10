EXEC = matex

MATEX    = ./$(EXEC).native
PROBE    = ../probe/probe.native
REGISTRY = $(RT_BASE_DIR)/matita.conf.xml \
           test/legacy_1.conf.xml test/ground_1.conf.xml test/basic_1.conf.xml
OBJS     = Make.objs
SRCS     = Make.srcs

DEVEL = ../../../matita/contribs/lambdadelta/basic_1/

test: test/$(SRCS)

test/$(OBJS): $(REGISTRY) Makefile
	@echo probe: $(DEVEL)
	$(H)$(PROBE) $(REGISTRY) -g $(DEVEL) -os > $@

test/$(SRCS): test/$(OBJS) $(REGISTRY) $(MATEX) Makefile
	@echo MaTeX: processing $<
	$(H)$(MATEX) -O test -l $(SRCS) -a -g -p $(REGISTRY) `cat $<`

.PHONY: test
