EXECS = roles

REQUIRES =

include ../Makefile.common

test:
	@./roles.native -C ../.. -r -p

up-css:
	@scp roles.css lahar.helm.cs.unibo.it:/projects/helm/public_html/lambdadelta/css/

up-js:
	@scp roles.js lahar.helm.cs.unibo.it:/projects/helm/public_html/lambdadelta/js/

.PHONY: test up-css up-js
