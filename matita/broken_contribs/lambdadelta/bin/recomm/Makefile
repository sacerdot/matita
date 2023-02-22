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

subst: subst.txt
	@sed s/://g <subst_cn.txt >subst.txt  
	@cd ../token; . ./subst.sh

recommGc%.ml recommGc%.mli: %.mrc mrc*.ml mrc*.mli
	@./mrc.native $<

.PHONY: test mrc subst
