PACKAGE = cic
PREDICATES =

INTERFACE_FILES = \
	cicUniv.mli		\
	unshare.mli             \
	deannotate.mli		\
	cicParser.mli		\
	cicUtil.mli		\
	helmLibraryObjects.mli  \
	libraryObjects.mli      \
	cic_indexable.mli \
	path_indexing.mli       \
	cicInspect.mli \
	cicPp.mli
IMPLEMENTATION_FILES = \
	cic.ml $(INTERFACE_FILES:%.mli=%.ml)
EXTRA_OBJECTS_TO_INSTALL = cic.ml cic.cmi
EXTRA_OBJECTS_TO_CLEAN =

include ../../Makefile.defs
include ../Makefile.common
