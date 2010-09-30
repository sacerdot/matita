PACKAGE = metadata
PREDICATES =

INTERFACE_FILES = \
	sqlStatements.mli \
	metadataTypes.mli \
	metadataExtractor.mli \
	metadataPp.mli \
	metadataConstraints.mli \
	metadataDb.mli \
	metadataDeps.mli \
	$(NULL)
IMPLEMENTATION_FILES = $(INTERFACE_FILES:%.mli=%.ml)
EXTRA_OBJECTS_TO_INSTALL =
EXTRA_OBJECTS_TO_CLEAN =

include ../../Makefile.defs
include ../Makefile.common
