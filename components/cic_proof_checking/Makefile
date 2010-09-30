
PACKAGE = cic_proof_checking
PREDICATES =

REDUCTION_IMPLEMENTATION = cicReductionMachine.ml

INTERFACE_FILES = \
	cicLogger.mli \
	cicEnvironment.mli \
	cicPp.mli \
	cicUnivUtils.mli \
	cicSubstitution.mli \
	cicMiniReduction.mli \
	cicReduction.mli \
	cicTypeChecker.mli \
        freshNamesGenerator.mli \
        cicDischarge.mli        \
	$(NULL)
IMPLEMENTATION_FILES = $(INTERFACE_FILES:%.mli=%.ml)

# Metadata tools only need zeta-reduction
EXTRA_OBJECTS_TO_INSTALL = \
            cicSubstitution.cmo cicSubstitution.cmx cicSubstitution.o \
            cicMiniReduction.cmo cicMiniReduction.cmx cicMiniReduction.o
EXTRA_OBJECTS_TO_CLEAN =

include ../../Makefile.defs
include ../Makefile.common
