DATE=$(shell date +%y%m%d)
VERSION=1.0.0
DIST=matitaprover---$(VERSION)

all:
	ocamlbuild matitaprover.native

clean:
	ocamlbuild -clean
	rm -rf $(DIST) $(DIST).tgz

dist:
	mkdir -p $(DIST)/Sources
	cp ReadMe $(DIST)
	cp *.ml *.mli *.mll *.mly Makefile _tags $(DIST)/Sources
	cd $(DIST); ln -s Sources/matitaprover.native matitaprover
	tar -cvzf $(DIST).tgz $(DIST)
