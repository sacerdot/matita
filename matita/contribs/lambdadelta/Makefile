OPEN := (
H    := @

TRIM := sed "s/ \\+$$//"

XOA_CONF     := ground_2/xoa.conf.xml
XOA_TARGETS  := ground_2/notation/xoa_notation.ma ground_2/xoa/xoa.ma

XOA_DIR      := ../../../components/binaries/xoa
XOA          := xoa.native
XOA_OPTS     := ../../matita.conf.xml $(XOA_CONF)

XOA2_CONF    := ground_2/xoa2.conf.xml
XOA2_TARGETS := ground_2/notation/xoa2_notation.ma ground_2/xoa/xoa2.ma
XOA2_OPTS    := ../../matita.conf.xml $(XOA2_CONF)

DEP_INPUT    := .depend
DEP_DIR      := ../../../components/binaries/matitadep
DEP          := matitadep.native
DEP_OPTS     :=

MAC_DIR      := ../../../components/binaries/mac
MAC          := mac.native
MAC_OPTS     :=

PRB_DIR      := ../../../components/binaries/probe
PRB          := probe.native
PRB_OPTS     := $(XOA_OPTS) -g 

ORIG         := . ./orig.sh 
ORIGS        := basic_2/basic_1.orig

CONTRIB      := lambdadelta_2

TAGS := all xoa xoa2 orig elim deps top leaf stats tbls trim contrib

PACKAGES  := ground_2 basic_2 apps_2 alpha_1
XPACKAGES := ground_2 basic_2

LDWS := $(shell find -name "*.ldw.xml")
TBLS := $(shell find -name "*.tbl")

all:
	../../matitac.opt

# MAS ########################################################################

define MAS_TEMPLATE
  MAS_$(1) := $$(shell find $(1) -name "*.ma")
  MAS      += $$(MAS_$(1))

$(1)/$(1)_probe.txt: $$(MAS_$(1))
	@echo "  PROBE $(1)"
	$$(H)$$(PRB_DIR)/$$(PRB) $$(PRB_OPTS) $(1) -sn -on -i > $$@

$(1)/$(1)_mac.txt: $$(MAS_$(1))
	@echo "  MAC $(1)"
	$$(H)$$(MAC_DIR)/$$(MAC) $$(MAC_OPTS) $$^ > $$@
endef

$(foreach PKG, $(PACKAGES), $(eval $(call MAS_TEMPLATE,$(PKG))))

# XMAS #######################################################################

define XMAS_TEMPLATE
  XMAS += $$(MAS_$(1))
endef

$(foreach PKG, $(XPACKAGES), $(eval $(call XMAS_TEMPLATE,$(PKG))))

# xoa ########################################################################

xoa: $(XOA_TARGETS)

$(XOA_TARGETS): $(XOA_CONF)
	@echo "  EXEC $(XOA) $(XOA_CONF)"
	$(H)MATITA_RT_BASE_DIR=../.. $(XOA_DIR)/$(XOA) $(XOA_OPTS)

# xoa2 #######################################################################

xoa2: $(XOA2_TARGETS)

$(XOA2_TARGETS): $(XOA2_CONF)
	@echo "  EXEC $(XOA) $(XOA2_CONF)"
	$(H)MATITA_RT_BASE_DIR=../.. $(XOA_DIR)/$(XOA) $(XOA2_OPTS)

# elim #######################################################################

elim:
	@echo "  GREP elim"
	$(H)grep "elim (.*?)" $(MAS) || true

# orig #######################################################################

orig: $(ORIGS)
	@echo "  ORIG basic_2"
	$(H)$(ORIG) basic_2 < $<

# dep input ##################################################################

$(DEP_INPUT): $(MAS)
	@echo "  GREP include"
	$(H)grep "include \"" $^ > $(DEP_INPUT)

# dep ########################################################################

deps: $(DEP_INPUT)
	@echo "  MATITADEP -c"
	$(H)$(DEP_DIR)/$(DEP) -c $(DEP_OPTS) < $<

# top ########################################################################

top: $(DEP_INPUT)
	@echo "  MATITADEP -t"
	$(H)$(DEP_DIR)/$(DEP) -t $(DEP_OPTS) < $<

# leaf #######################################################################

leaf: $(DEP_INPUT)
	@echo "  MATITADEP -l"
	$(H)$(DEP_DIR)/$(DEP) -l $(DEP_OPTS) < $<

# stats ######################################################################

define STATS_TEMPLATE
  STT_$(1) := $(1).stats
  STTS     += $$(STT_$(1))

  $$(STT_$(1)): S0  = $$(shell cat $(1)/$(1)_probe.txt)
  $$(STT_$(1)): S1  = $$(shell cat $(1)/$(1)_mac.txt)
  $$(STT_$(1)): S4  = $$(shell ls $$(MAS_$(1)) | wc -l)
  $$(STT_$(1)): P1  = $$(shell grep "^theorem " $$(MAS_$(1)) | wc -l)
  $$(STT_$(1)): P2  = $$(shell grep "^lemma " $$(MAS_$(1)) | wc -l)
  $$(STT_$(1)): P3  = $$(shell grep "^fact " $$(MAS_$(1)) | wc -l)
  $$(STT_$(1)): P4  = $$(shell grep qed $$(MAS_$(1)) | wc -l)
  $$(STT_$(1)): C1  = $$(shell grep "^inductive \|^record " $$(MAS_$(1)) | wc -l)
  $$(STT_$(1)): C2  = $$(shell grep "^definition \|^let rec " $$(MAS_$(1)) | wc -l)
  $$(STT_$(1)): M1  = $$(shell grep "^axiom " $$(MAS_$(1)) | wc -l)
  $$(STT_$(1)): M2  = $$(shell grep "$$(OPEN)\*[^*:]*$$$$" $$(MAS_$(1)) | wc -l)
  $$(STT_$(1)): M3  = $$(shell grep "(\*\*)" $$(MAS_$(1)) | wc -l)

$$(STT_$(1)): $$(MAS_$(1)) $(1)/$(1)_probe.txt $(1)/$(1)_mac.txt
	@printf '\x1B[1;40;37m'
	@printf '%-15s %-47s' 'Statistics for:' $(1)
	@printf '\x1B[0m\n'
	@printf '\x1B[1;40;35m'
	@printf '%-8s %6i' Chars $$(word 1, $$(S1))
	@printf '   %-8s %4i' Pages $$(word 2, $$(S1))
	@printf '   %-7s %7i' Nodes $$(word 3, $$(S0))
	@printf '   %-11s' ''
	@printf '\x1B[0m\n'
	@printf '\x1B[1;40;36m'
	@printf '%-8s %6i' Files $$(S4)
	@printf '   %-8s %4i' Sources $$(word 1, $$(S0))
	@printf '   %-7s %7i' Objects $$(word 2, $$(S0))
	@printf '   %-11s' ''
	@printf '\x1B[0m\n'	
	@printf '\x1B[1;40;32m'
	@printf '%-8s %6i' Theorems $$(P1)
	@printf '   %-8s %4i' Lemmas $$(P2)
	@printf '   %-7s %7i' Facts $$(P3)
	@printf '   %-6s %4i' Proofs $$(P4)
	@printf '\x1B[0m\n'	
	@printf '\x1B[1;40;33m'
	@printf '%-8s %6i' Declared $$(C1)
	@printf '   %-8s %4i' Defined $$(C2)	
	@printf '   %-29s' ''
	@printf '\x1B[0m\n'
	@printf '\x1B[1;40;31m'
	@printf '%-8s %6i' Axioms $$(M1)
	@printf '   %-8s %4i' Comments $$(M2)
	@printf '   %-7s %7i' Marks $$(M3)
	@printf '   %-11s' ''
	@printf '\x1B[0m\n'

.PHONY: $$(STT_$(1))
endef

ifeq ($(MAKECMDGOALS), stats)
   $(foreach PKG, $(PACKAGES), $(eval $(call STATS_TEMPLATE,$(PKG))))
endif

stats: $(STTS)

# summary ####################################################################

define SUMMARY_TEMPLATE
  SUM_$(1) := $(1)/web/$(1)_sum.tbl  
  SUMS     += $$(SUM_$(1))

  $$(SUM_$(1)): S0 = $$(shell cat $(1)/$(1)_probe.txt)
  $$(SUM_$(1)): S1 = $$(shell cat $(1)/$(1)_mac.txt)
  $$(SUM_$(1)): S4 = $$(shell ls $$(MAS_$(1)) | wc -l)
  $$(SUM_$(1)): C1 = $$(shell grep "^inductive \|^record " $$(MAS_$(1)) | wc -l)
  $$(SUM_$(1)): C2 = $$(shell grep "^definition \|^let rec " $$(MAS_$(1)) | wc -l)
  $$(SUM_$(1)): C3 = $$(shell grep "^inductive \|^record \|^definition \|^let rec " $$(MAS_$(1)) | wc -l)
  $$(SUM_$(1)): P1 = $$(shell grep "^theorem " $$(MAS_$(1)) | wc -l)
  $$(SUM_$(1)): P2 = $$(shell grep "^lemma " $$(MAS_$(1)) | wc -l)
  $$(SUM_$(1)): P3 = $$(shell grep "^lemma \|^theorem " $$(MAS_$(1)) | wc -l)

  $$(SUM_$(1)): $$(MAS_$(1)) $(1)/$(1)_probe.txt $(1)/$(1)_mac.txt
	@printf '  SUMMARY $(1)\n'
	@printf 'name "$$(basename $$(@F))"\n\n'                  >  $$@
	@printf 'table {\n'                                       >> $$@
	@printf '   class "gray"   [ "category"\n'                >> $$@
	@printf '      [ "objects" * ]\n'                         >> $$@
	@printf '   ]\n'                                          >> $$@
	@printf '   class "cyan"   [ "sizes"\n'                   >> $$@
	@printf '      [ "files"      "$$(S4)" ]\n'               >> $$@
	@printf '      [ "characters" "$$(word 1, $$(S1))" ]\n'   >> $$@
	@printf '      [ "nodes"      "$$(word 3, $$(S0))" ]\n'   >> $$@
	@printf '   ]\n'                                          >> $$@	
	@printf '   class "green"  [ "propositions"\n'            >> $$@
	@printf '      [ "theorems" "$$(P1)" ]\n'                 >> $$@
	@printf '      [ "lemmas"   "$$(P2)" ]\n'                 >> $$@
	@printf '      [ "total"    "$$(P3)" ]\n'                 >> $$@
	@printf '   ]\n'                                          >> $$@
	@printf '   class "yellow" [ "concepts"\n'                >> $$@
	@printf '      [ "declared" "$$(C1)" ]\n'                 >> $$@
	@printf '      [ "defined"  "$$(C2)" ]\n'                 >> $$@
	@printf '      [ "total"    "$$(C3)" ]\n'                 >> $$@
	@printf '   ]\n'                                          >> $$@
	@printf '}\n\n'                                           >> $$@
	@printf 'class "capitalize italic" { 0 }\n\n'             >> $$@
	@printf 'class "italic"            { 1 } { 3 } { 5 }\n\n' >> $$@
	@printf 'class "right italic"      { 2 } { 4 } { 6 }\n'   >> $$@

.PHONY: $$(SUM_$(1))
endef

ifeq ($(MAKECMDGOALS), tbls)
   $(foreach PKG, $(PACKAGES), $(eval $(call SUMMARY_TEMPLATE,$(PKG))))
endif

tbls: $(SUMS)

# trim #######################################################################

TRIMS := $(MAS) $(TBLS) $(LDWS)

%.trimmed: %
	$(H)expand $< | $(TRIM) > $@
	$(H)if diff $< $@ > /dev/null; then $(RM) $@; else echo "  TRIM $<" & mv $@ $<; fi

trim: $(TRIMS:%=%.trimmed)

# contrib ####################################################################

contrib:
	@echo "  TAR -czf $(CONTRIB).tar.gz root $(XPACKAGES)"
	$(H)tar -czf $(CONTRIB).tar.gz root $(XMAS)

##############################################################################

.PHONY: $(TAGS)

.SUFFIXES:
