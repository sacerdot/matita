PACKAGE = content
PREDICATES =

INTERFACE_FILES =		\
	content.mli		\
	cicNotationUtil.mli	\
	cicNotationEnv.mli	\
	cicNotationPp.mli	\
	interpretations.mli \
	$(NULL)
IMPLEMENTATION_FILES =		\
	cicNotationPt.ml	\
	$(INTERFACE_FILES:%.mli=%.ml)

include ../../Makefile.defs
include ../Makefile.common
