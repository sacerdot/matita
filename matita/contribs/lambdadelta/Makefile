OPEN := (
H    := @

TRIM := sed "s/ \\+$$//"

XOA_CONF     := ground_2/xoa.conf.xml
XOA_TARGETS  := ground_2/notation/xoa/notation.ma ground_2/xoa/xoa.ma

XOA_DIR      := ../../../components/binaries/xoa
XOA          := xoa.native
XOA_OPTS     := ../../matita.conf.xml $(XOA_CONF)

XOA2_CONF    := ground_2/xoa2.conf.xml
XOA2_OPTS    := ../../matita.conf.xml $(XOA2_CONF)

DEP_INPUT    := .depend
DEP_DIR      := ../../../components/binaries/matitadep
DEP          := matitadep.native
DEP_OPTS     :=

PRB_DIR      := ../../../components/binaries/probe
PRB          := probe.native
PRB_OPTS     := $(XOA_OPTS) -g -i

ORIG         := . ./orig.sh 
ORIGS        := basic_2/basic_1.orig

CONTRIB      := lambdadelta_2

WWW          := ../../../../helm/www/lambdadelta

TAGS := all xoa xoa2 orig elim deps top leaf stats tbls trim contrib clean \
        www up-html

PACKAGES  := ground_2 basic_2 static_2 apps_2 alpha_1
XPACKAGES := ground_2 basic_2

LDWS := $(shell find -name "*.ldw.xml")
TBLS := $(shell find -name "*.tbl")

all:
	@echo "  MATITAC $(PACKAGES)"
	$(H)../../matitac.opt $(PACKAGES)

# MAS ########################################################################

define MAS_TEMPLATE
  MAS_$(1) := $$(shell find $(1) -name "*.ma")
  MAS      += $$(MAS_$(1))

$(1)/$(1)_probe.txt: $$(MAS_$(1))
	@echo "  PROBE $(1)"
	$$(H)$$(PRB_DIR)/$$(PRB) $$(PRB_OPTS) $(1) -sn -sc -on -oc -f > $$@
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
	$(H)$(XOA_DIR)/$(XOA) $(XOA_OPTS)

# xoa2 #######################################################################

xoa2: $(XOA2_CONF)
	@echo "  EXEC $(XOA) $(XOA2_CONF)"
	$(H)MATITA_RT_BASE_DIR=../.. $(XOA_DIR)/$(XOA) -s $(XOA2_OPTS)

# elim #######################################################################

elim:
	@echo "  GREP elim"
	$(H)grep "elim (.*?)" $(MAS) || true

# orig #######################################################################

orig: $(ORIGS)
	@echo "  ORIG basic_2"
	$(H)$(ORIG) basic_2 < $<

# dep input ##################################################################

$(DEP_INPUT): LINE = $(MAS:%=%:include \"\".)

$(DEP_INPUT): $(MAS) Makefile
	@echo "  GREP include"
	$(H)grep "include \"" $^ > $(DEP_INPUT)
	$(H)echo "$(LINE)" | sed -e 's/\"\. /\"\.\n/g' >> $(DEP_INPUT) 

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

  $$(STT_$(1)): C0 = $$(shell cat $(1)/$(1)_probe.txt)
  $$(STT_$(1)): C2 = $$(word 2, $$(C0))
  $$(STT_$(1)): C3 = $$(word 4, $$(C0))
  $$(STT_$(1)): O1 = $$(shell ls $$(MAS_$(1)) | wc -l)
  $$(STT_$(1)): O2 = $$(word 1, $$(C0))
  $$(STT_$(1)): O3 = $$(word 3, $$(C0))
  $$(STT_$(1)): P1 = $$(word 10, $$(C0))
  $$(STT_$(1)): P2 = $$(word 9, $$(C0))
  $$(STT_$(1)): P3 = $$(word 8, $$(C0))
  $$(STT_$(1)): P4 = $$(shell grep "qed[.-]" $$(MAS_$(1)) | wc -l)
  $$(STT_$(1)): D1 = $$(word 5, $$(C0))
  $$(STT_$(1)): D2 = $$(word 7, $$(C0))
  $$(STT_$(1)): D3 = $$(shell grep "defined[.-]" $$(MAS_$(1)) | wc -l)  
  $$(STT_$(1)): M1 = $$(word 6, $$(C0))
  $$(STT_$(1)): M2 = $$(shell grep "$$(OPEN)\*[^*:]*$$$$" $$(MAS_$(1)) | wc -l)
  $$(STT_$(1)): M3 = $$(shell grep "(\*\*)" $$(MAS_$(1)) | wc -l)

$$(STT_$(1)): $$(MAS_$(1)) $(1)/$(1)_probe.txt
	@printf '\x1B[1;40;37m'
	@printf '%-15s %-46s' 'Statistics for:' $(1)
	@printf '\x1B[0m\n'
	@printf '\x1B[1;40;35m'
	@printf '%-12s' '' 
	@printf '   %-8s %6i' Chars $$(C2)
	@printf '   %-7s %7i' Nodes $$(C3)
	@printf '   %-11s' ''
	@printf '\x1B[0m\n'
	@printf '\x1B[1;40;36m'
	@printf '%-8s %3i' Files $$(O1)
	@printf '   %-8s %6i' Sources $$(O2)
	@printf '   %-7s %7i' Objects $$(O3)
	@printf '   %-11s' ''
	@printf '\x1B[0m\n'	
	@printf '\x1B[1;40;32m'
	@printf '%-8s %3i' Theorems $$(P1)
	@printf '   %-8s %6i' Lemmas $$(P2)
	@printf '   %-7s %7i' Facts $$(P3)
	@printf '   %-6s %4i' Proofs $$(P4)
	@printf '\x1B[0m\n'	
	@printf '\x1B[1;40;33m'
	@printf '%-8s %3i' Declared $$(D1)
	@printf '   %-8s %6i' Defined $$(D2)	
	@printf '   %-7s %7i' Proved $$(D3)
	@printf '   %-11s' ''
	@printf '\x1B[0m\n'
	@printf '\x1B[1;40;31m'
	@printf '%-8s %3i' Axioms $$(M1)
	@printf '   %-8s %6i' Comments $$(M2)
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

  $$(SUM_$(1)): C0 = $$(shell cat $(1)/$(1)_probe.txt)
  $$(SUM_$(1)): S1 = $$(word 1, $$(C0))
  $$(SUM_$(1)): S2 = $$(word 2, $$(C0))
  $$(SUM_$(1)): S3 = $$(word 3, $$(C0))
  $$(SUM_$(1)): S4 = $$(word 4, $$(C0))
  $$(SUM_$(1)): S5 = $$(shell printf "%.1f" `echo "scale=2;$$(S4)/$$(S2)"|bc`)
  $$(SUM_$(1)): C1 = $$(word 5, $$(C0))
  $$(SUM_$(1)): C2 = $$(word 7, $$(C0))
  $$(SUM_$(1)): C3 = $$(shell echo "$$(C1)+$$(C2)"|bc)
  $$(SUM_$(1)): P1 = $$(word 10, $$(C0))
  $$(SUM_$(1)): P2 = $$(word 9, $$(C0))
  $$(SUM_$(1)): P3 = $$(shell echo "$$(P1)+$$(P2)"|bc)

  $$(SUM_$(1)): $$(MAS_$(1)) $(1)/$(1)_probe.txt Makefile
	@printf '  SUMMARY $(1)\n'
	@printf 'name "$$(basename $$(@F))"\n\n'                        >  $$@
	@printf 'table {\n'                                             >> $$@
	@printf '   class "gray"  [ "category"\n'                       >> $$@
	@printf '      [ "units" * ]\n'                                 >> $$@
	@printf '   ]\n'                                                >> $$@
	@printf '   class "water" [ "sizes"\n'                          >> $$@
	@printf '      [ "characters (files)"    "$$(S2) ($$(S1))" ]\n' >> $$@
	@printf '      [ "nodes (objects)"       "$$(S4) ($$(S3))" ]\n' >> $$@
	@printf '      [ "intrinsic loss factor" "$$(S5)" ]\n'          >> $$@
	@printf '   ]\n'                                                >> $$@	
	@printf '   class "green" [ "propositions"\n'                   >> $$@
	@printf '      [ "theorems" "$$(P1)" ]\n'                       >> $$@
	@printf '      [ "lemmas"   "$$(P2)" ]\n'                       >> $$@
	@printf '      [ "total"    "$$(P3)" ]\n'                       >> $$@
	@printf '   ]\n'                                                >> $$@
	@printf '   class "grass" [ "concepts"\n'                       >> $$@
	@printf '      [ "declared" "$$(C1)" ]\n'                       >> $$@
	@printf '      [ "defined"  "$$(C2)" ]\n'                       >> $$@
	@printf '      [ "total"    "$$(C3)" ]\n'                       >> $$@
	@printf '   ]\n'                                                >> $$@
	@printf '}\n\n'                                                 >> $$@
	@printf 'class "capitalize italic" { 0 }\n\n'                   >> $$@
	@printf 'class "italic"            { 1 } { 3 } { 5 }\n\n'       >> $$@
	@printf 'class "right italic"      { 2 } { 4 } { 6 }\n'         >> $$@

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

# clean ######################################################################

clean:
	$(H)$(RM) `find -name "*~" -type f -print`

# www ######################################################################

www:
	$(H)$(MAKE) --no-print-directory -C $(WWW) www

# www ######################################################################

up-html:
	$(H)$(MAKE) --no-print-directory -C $(WWW) up-html

##############################################################################

.PHONY: $(TAGS)

.SUFFIXES:
