EXECS = mrc recomm

REQUIRES =

include ../Makefile.common

clean::
	@$(RM) recommGc*.ml*

test:
	@./recomm.native $(O) -C ../../ground/steps . | sort | uniq > log.txt

MRCS = $(wildcard *.mrc)

mrc: $(MRCS:%.mrc=recommGc%.ml)
	@./mrc.native .

recommGc%.ml recommGc%.mli: %.mrc mrc.ml
	@./mrc.native $<

.PHONY: test mrc
