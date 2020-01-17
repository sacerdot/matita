EXECS = inline

REQUIRES =

include ../Makefile.common

test:
	@./inline.native -p ../lambdadelta/*/deps.txt > deps.txt
	@../matitadep/matitadep.native -c ../lambdadelta/.depend deps.txt > redundant.txt
	@./inline.native -i -b ../lambdadelta redundant.txt ../lambdadelta/*/deps.txt

.PHONY: test
