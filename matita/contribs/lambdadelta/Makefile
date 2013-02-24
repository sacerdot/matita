OPEN = (

H        = @
XOA_DIR  = ../../../components/binaries/xoa
XOA      = xoa.native
DEP_DIR  = ../../../components/binaries/matitadep
DEP      = matitadep.native
MAC_DIR  = ../../../components/binaries/mac
MAC      = mac.native
PRB_DIR  = ../../../components/binaries/probe
PRB      = probe.native
PRB_OPTS = ../../matita.conf.xml -g

XOA_CONF    = ground_2/xoa.conf.xml
XOA_TARGETS = ground_2/xoa_notation.ma ground_2/xoa.ma

ORIG     = . ./orig.sh 

ORIGS    = basic_2/basic_1.orig

PACKAGES = ground_2 basic_2 apps_2

all:
	../../matitac.opt

# MAS ########################################################################

define MAS_TEMPLATE
  MAS_$(1) := $$(shell find $(1) -name "*.ma")
  MAS      += $$(MAS_$(1))
endef

$(foreach PKG, $(PACKAGES), $(eval $(call MAS_TEMPLATE,$(PKG))))

# xoa ########################################################################

xoa: $(XOA_TARGETS)

$(XOA_TARGETS): $(XOA_CONF)
	@echo "  EXEC $(XOA) $(XOA_CONF)"
	$(H)MATITA_RT_BASE_DIR=../.. $(XOA_DIR)/$(XOA) $(XOA_CONF)

# orig #######################################################################

orig: $(ORIGS)
	@echo "  ORIG basic_2"
	$(H)$(ORIG) basic_2 < $(ORIGS)

# dep ########################################################################

deps: $(DEP_DIR)/$(DEP)
	@echo "  MATITADEP"
	$(H)grep "include \"" $(MAS) | $<

# stats ######################################################################

define STATS_TEMPLATE
  STT_$(1) := $(1).stats
  STTS     += $$(STT_$(1))

  $$(STT_$(1)): S1 = $$(shell $$(MAC_DIR)/$$(MAC) $$(MAS_$(1)))
  $$(STT_$(1)): S2 := $$(shell echo $$$$(($$(S1) / 5120)))
  $$(STT_$(1)): S4 := $$(shell ls $$(MAS_$(1)) | wc -l)
  $$(STT_$(1)): S5 := $$(shell $$(PRB_DIR)/$$(PRB) $$(PRB_OPTS) $(1) -sn -on)  
  $$(STT_$(1)): P1 := $$(shell grep "theorem " $$(MAS_$(1)) | wc -l)
  $$(STT_$(1)): P2 := $$(shell grep "lemma " $$(MAS_$(1)) | wc -l)
  $$(STT_$(1)): P3 := $$(shell grep "fact " $$(MAS_$(1)) | wc -l)
  $$(STT_$(1)): P4 := $$(shell grep qed $$(MAS_$(1)) | wc -l)
  $$(STT_$(1)): C1 := $$(shell grep "inductive \|record " $$(MAS_$(1)) | wc -l)
  $$(STT_$(1)): C2 := $$(shell grep "definition \|let rec " $$(MAS_$(1)) | wc -l)
  $$(STT_$(1)): M1 := $$(shell grep "axiom " $$(MAS_$(1)) | wc -l)
  $$(STT_$(1)): M2 := $$(shell grep "$$(OPEN)\*[^*:]*$$$$" $$(MAS_$(1)) | wc -l)
  $$(STT_$(1)): M3 := $$(shell grep "(\*\*)" $$(MAS_$(1)) | wc -l)

$$(STT_$(1)):
	@printf '\x1B[1;40;37m'
	@printf '%-15s %-44s' 'Statistics for:' $(1)
	@printf '\x1B[0m\n'
	@printf '\x1B[1;40;35m'
	@printf '%-8s %6i' Chars $$(S1)
	@printf '   %-8s %4i' Pages $$(S2)
	@printf '   %-26s' ''
	@printf '\x1B[0m\n'
	@printf '\x1B[1;40;36m'
	@printf '%-8s %6i' Files $$(S4)
	@printf '   %-8s %4i' Sources $$(word 1, $$(S5))	
	@printf '   %-7s %4i' Objects $$(word 2, $$(S5))
	@printf '   %-11s' ''
	@printf '\x1B[0m\n'	
	@printf '\x1B[1;40;32m'
	@printf '%-8s %6i' Theorems $$(P1)
	@printf '   %-8s %4i' Lemmas $$(P2)
	@printf '   %-7s %4i' Facts $$(P3)
	@printf '   %-6s %4i' Proofs $$(P4)
	@printf '\x1B[0m\n'	
	@printf '\x1B[1;40;33m'
	@printf '%-8s %6i' Declared $$(C1)
	@printf '   %-8s %4i' Defined $$(C2)	
	@printf '   %-26s' ''
	@printf '\x1B[0m\n'
	@printf '\x1B[1;40;31m'
	@printf '%-8s %6i' Axioms $$(M1)
	@printf '   %-8s %4i' Comments $$(M2)
	@printf '   %-7s %4i' Marks $$(M3)
	@printf '   %-11s' ''
	@printf '\x1B[0m\n'
endef

ifeq ($(MAKECMDGOALS), stats)
   $(foreach PKG, $(PACKAGES), $(eval $(call STATS_TEMPLATE,$(PKG))))
endif

stats: $(STTS)

# summary ####################################################################

define SUMMARY_TEMPLATE
  TBL_$(1) := $(1)/$(1)_sum.tbl  
  TBLS     += $$(TBL_$(1))

  $$(TBL_$(1)): S1 := $$(shell ls $$(MAS_$(1)) | wc -l)
  $$(TBL_$(1)): S2 := $$(shell $$(MAC_DIR)/$$(MAC) $$(MAS_$(1)))
  $$(TBL_$(1)): S3 := $$(shell $$(PRB_DIR)/$$(PRB) $$(PRB_OPTS) $(1) -i)
  $$(TBL_$(1)): C1 := $$(shell grep "inductive \|record " $$(MAS_$(1)) | wc -l)
  $$(TBL_$(1)): C2 := $$(shell grep "definition \|let rec " $$(MAS_$(1)) | wc -l)
  $$(TBL_$(1)): C3 := $$(shell grep "inductive \|record \|definition \|let rec " $$(MAS_$(1)) | wc -l)
  $$(TBL_$(1)): P1 := $$(shell grep "theorem " $$(MAS_$(1)) | wc -l)
  $$(TBL_$(1)): P2 := $$(shell grep "lemma " $$(MAS_$(1)) | wc -l)
  $$(TBL_$(1)): P3 := $$(shell grep "lemma \|theorem " $$(MAS_$(1)) | wc -l)

  $$(TBL_$(1)): $$(MAS_$(1))
	@printf '  SUMMARY $(1)\n'
	@printf 'name "$$(basename $$(@F))"\n\n'       >  $$@
	@printf 'table {\n'                            >> $$@
	@printf '   class "grey" [ "category"\n'       >> $$@
	@printf '      [ "objects" * ]\n'              >> $$@
	@printf '   ]\n'                               >> $$@
	@printf '   class "cyan" [ "sizes"\n'          >> $$@
	@printf '      [ "files" "$$(S1)" ]\n'         >> $$@
	@printf '      [ "characters" "$$(S2)" ]\n'    >> $$@
	@printf '      [ "nodes" "$$(S3)" ]\n'         >> $$@
	@printf '   ]\n'                               >> $$@	
	@printf '   class "green" [ "propositions"\n'  >> $$@
	@printf '      [ "theorems" "$$(P1)" ]\n'      >> $$@
	@printf '      [ "lemmas"   "$$(P2)" ]\n'      >> $$@
	@printf '      [ "total"    "$$(P3)" ]\n'      >> $$@
	@printf '   ]\n'                               >> $$@
	@printf '   class "yellow" [ "concepts"\n'     >> $$@
	@printf '      [ "declared" "$$(C1)" ]\n'      >> $$@
	@printf '      [ "defined"  "$$(C2)" ]\n'      >> $$@
	@printf '      [ "total"    "$$(C3)" ]\n'      >> $$@
	@printf '   ]\n'                               >> $$@
	@printf '}\n\n'                                >> $$@
	@printf 'class "component" { 0 }\n\n'          >> $$@
	@printf 'class "plane" { 1 } { 3 } { 5 }\n\n'  >> $$@
	@printf 'class "number" { 2 } { 4 } { 6 }\n\n' >> $$@
endef

ifeq ($(MAKECMDGOALS), tbls)
   $(foreach PKG, $(PACKAGES), $(eval $(call SUMMARY_TEMPLATE,$(PKG))))
endif

tbls: $(TBLS)
