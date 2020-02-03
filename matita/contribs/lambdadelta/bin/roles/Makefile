EXECS = roles

REQUIRES =

include ../Makefile.common

test:
	@./roles.native -C ../.. -r -W > roles.html

up-css:
	@scp roles.css lahar.helm.cs.unibo.it:/projects/helm/public_html/lambdadelta/css/

.PHONY: test up-css
