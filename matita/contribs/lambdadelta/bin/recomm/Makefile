EXECS = mrc recomm

REQUIRES =

include ../Makefile.common

clean::
	@$(RM) recommGc*.ml*

test:
	@./recomm.native -r $(O) -C srcs . | sort | uniq > log.txt

MRCS = $(wildcard *.mrc)

mrc: $(MRCS:%.mrc=recommGc%.ml)
	@./mrc.native .

recommGc%.ml recommGc%.mli: %.mrc mrc*.ml mrc*.mli
	@./mrc.native $<

.PHONY: test mrc
