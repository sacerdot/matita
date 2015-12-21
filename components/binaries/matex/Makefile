EXEC = matex
VERSION=0.1.0

REQUIRES = helm-ng_library

include ../Makefile.common

REGISTRY = $(RT_BASE_DIR)/matita.conf.xml

OBJ = cic:/matita/lambdadelta/basic_1/pr0/pr0/pr0_confluence.con

test:
	@echo MaTeX $(OBJ)
	$(H)./matex.native -O test $(REGISTRY) $(OBJ)

.PHONY: test
