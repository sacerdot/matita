EXEC = matex
VERSION=0.1.0

REQUIRES = helm-ng_library

include ../Makefile.common

REGISTRY = $(RT_BASE_DIR)/matita.conf.xml

OBJS = cic:/matita/lambdadelta/basic_1/pr0/pr0/pr0_confluence.con\
       cic:/matita/lambdadelta/basic_1/pr0/defs/pr0_ind.con

test:
	@echo MaTeX: $(OBJS:cic:/matita/lambdadelta/basic_1/pr0/%.con=%)
	$(H)./matex.native -O test -t -p $(REGISTRY) $(OBJS)

.PHONY: test
