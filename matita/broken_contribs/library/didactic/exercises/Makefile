
all:
	for X in *.ma; do $(MAKE) exercise-$$X; done

clean:
	rm exercise-*

exercise-%.ma: %.ma
	cp $< $@
	perl -ne 'undef $$/;s/\(\*BEGIN.*?END\*\)/…/msg;print' -i $@
	perl -ne 'undef $$/;s/\(\*DOCBEGIN.*?DOCEND\*\)//msg;print' -i $@
	(echo '<?xml version="1.0" encoding="UTF-8"?><html><head></meta http-equiv="Content-Type" content="text/html; charset=utf-8"><style type="text/css">pre, code { font-family: Sans; font-size: 1em; background-color:#efee79; } pre { margin-right: 5em;}</style></head><body>'; awk 'BEGIN { p = 0; } /DOCEND/ { p = 0; } { if (p == 1) print $$0; } /DOCBEGIN/ { p = 1;}' < $< | markdown; echo '</body></html>') > exercise-$*.html

