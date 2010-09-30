PACKAGE = tactics

INTERFACE_FILES = \
	proofEngineTypes.mli \
	proofEngineHelpers.mli proofEngineReduction.mli \
	continuationals.mli \
	tacticals.mli reductionTactics.mli proofEngineStructuralRules.mli \
	primitiveTactics.mli hashtbl_equiv.mli metadataQuery.mli \
	universe.mli \
	autoTypes.mli \
	autoCache.mli \
	paramodulation/utils.mli \
	closeCoercionGraph.mli \
	paramodulation/subst.mli \
	paramodulation/equality.mli\
	paramodulation/founif.mli\
	paramodulation/equality_indexing.mli\
	paramodulation/indexing.mli \
	paramodulation/saturation.mli \
	automationCache.mli \
	variousTactics.mli \
	compose.mli \
	introductionTactics.mli	eliminationTactics.mli negationTactics.mli \
	equalityTactics.mli \
	auto.mli \
	destructTactic.mli \
        inversion.mli inversion_principle.mli ring.mli setoids.mli \
	fourier.mli fourierR.mli fwdSimplTactic.mli history.mli \
	statefulProofEngine.mli tactics.mli declarative.mli

IMPLEMENTATION_FILES = $(INTERFACE_FILES:%.mli=%.ml)


all:

# we omit dependencies since it is a pain when distributing
tactics_mli_deps = tactics.ml *Tactics.mli *Tactic.mli fourierR.mli ring.mli paramodulation/indexing.mli
tactics.mli: tactics.ml
	$(H)echo "  OCAMLC -i $$(tactics_mli_deps) > $@"
	$(H)echo "(* GENERATED FILE, DO NOT EDIT. STAMP:`date` *)" > $@
	$(H)$(OCAMLC) -I paramodulation -i tactics.ml >> $@

UTF8DIR = $(shell $(OCAMLFIND) query helm-syntax_extensions)
STR=$(shell $(OCAMLFIND) query str)
MY_SYNTAXOPTIONS = -pp "camlp5o -I $(UTF8DIR) -I $(STR) str.cma pa_extend.cmo profiling_macros.cma -loc loc"
paramodulation/%.cmo: SYNTAXOPTIONS = $(MY_SYNTAXOPTIONS)
paramodulation/%.cmo: OCAMLC = $(OCAMLC_P4)
paramodulation/%.cmx: SYNTAXOPTIONS = $(MY_SYNTAXOPTIONS)
paramodulation/%.cmx: OCAMLOPT = $(OCAMLOPT_P4)

depend: SYNTAXOPTIONS = $(MY_SYNTAXOPTIONS)
depend.opt: SYNTAXOPTIONS = $(MY_SYNTAXOPTIONS)

STATS_EXCLUDE = tactics.mli

include ../../Makefile.defs
include ../Makefile.common

OCAMLOPTIONS+= -I paramodulation
OCAMLDEPOPTIONS+= -I paramodulation
#PREPROCOPTIONS:=
#OCAML_PROF=p -p a
