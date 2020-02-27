EXECS = inline

REQUIRES =

include ../Makefile.common

test:
	@./inline.native -p ../../*/deps.txt > deps.txt
	@../../../../../components/binaries/matitadep/matitadep.native -c ../../.depend deps.txt > redundant.txt
	@./inline.native -i -b ../.. redundant.txt ../../*/deps.txt

.PHONY: test
