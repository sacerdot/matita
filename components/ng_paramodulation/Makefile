PACKAGE = ng_paramodulation

INTERFACE_FILES = \
	terms.mli pp.mli foSubst.mli \
	orderings.mli foUtils.mli foUnif.mli index.mli superposition.mli \
	stats.mli paramod.mli nCicBlob.mli nCicProof.mli \
	nCicParamod.mli

IMPLEMENTATION_FILES = $(INTERFACE_FILES:%.mli=%.ml)

all: hash.o
opt: hash.o

hash.o:
	gcc -I `ocamlc -where`/caml/ -c hash.c

include ../../Makefile.defs
include ../Makefile.common
