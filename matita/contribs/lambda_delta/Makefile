H        = @
XOA_DIR  = ../../../components/binaries/xoa
XOA      = xoa.native

CONF     = ground_2/xoa.conf.xml
TARGETS  = ground_2/xoa_natation.ma ground_2/xoa.ma

ORIG     = . ./orig.sh 

ORIGS    = basic_2/basic_1.orig

PACKAGES = ground_2 basic_2 apps_2

all:

# xoa ########################################################################

xoa: $(TARGETS)

$(TARGETS): $(CONF)
	@echo "  EXEC $(XOA) $(CONF)"
	$(H)MATITA_RT_BASE_DIR=../.. $(XOA_DIR)/$(XOA) $(CONF)

# orig #######################################################################

orig: $(ORIGS)
	@echo "  ORIG basic_2"
	$(H)$(ORIG) basic_2 < $(ORIGS)

# stats ######################################################################

stats: $(PACKAGES:%=%.stats)

%.stats: MAS = $(shell find $* -name "*.ma")

%.stats: CHARS = $(shell cat $(MAS) | wc -c)

%.stats:
	@printf '\x1B[1;40;37m'
	@printf '%-15s %-42s' 'Statistics for:' $*	
	@printf '\x1B[0m\n'	
	@printf '\x1B[1;40;35m'
	@printf '%-8s %6i' Chars $(CHARS)
	@printf '   %-8s %5i' Lines `cat $(MAS) | wc -l`
	@printf '   %-6s %3i' Pages `echo $$(($(CHARS) / 5120))`
	@printf '   %-10s' ''
	@printf '\x1B[0m\n'
	@printf '\x1B[1;40;36m'
	@printf '%-8s %6i' Sources `ls $(MAS) | wc -l`
	@printf '   %-40s' ''
#	@printf '   %-8s %5i' Objs `ls *.vo | wc -l`
#	@printf '   %-6s %3i' Files `ls *.v | wc -l`
	@printf '\x1B[0m\n'	
	@printf '\x1B[1;40;32m'
	@printf '%-8s %6i' Theorems `grep "theorem " $(MAS) | wc -l`
	@printf '   %-8s %5i' Lemmas `grep "lemma " $(MAS) | wc -l`
	@printf '   %-6s %3i' Facts `grep "fact " $(MAS) | wc -l`
	@printf '   %-6s %3i' Proofs `grep qed $(MAS) | wc -l`
	@printf '\x1B[0m\n'	
	@printf '\x1B[1;40;33m'
	@printf '%-8s %6i' Defs `grep "definition\|let rec\|inductive\|record" $(MAS) | wc -l` 
	@printf '   %-40s' ''
#	@printf '   %-8s %5i' Local `grep "Local" *.v | wc -l`
	@printf '\x1B[0m\n'
	@printf '\x1B[1;40;31m'
	@printf '%-8s %6i' Axioms `grep axiom $(MAS) | wc -l`
	@printf '   %-8s %5i' Comments `grep "(\*[^*:]*$$" $(MAS) | wc -l`
	@printf '   %-6s %3i' Marks `grep "(\*\*)" $(MAS) | wc -l`
	@printf '   %-10s' ''
	@printf '\x1B[0m\n'

# summary ####################################################################

define SUMMARY_TEMPLATE
  TBL_$(1) := $(1)/$(1)_sum.tbl  
  MAS_$(1) := $$(shell find $(1) -name "*.ma")
  TBLS     += $$(TBL_$(1))

  $$(TBL_$(1)): V1 := $$(shell ls $$(MAS_$(1)) | wc -l)
  $$(TBL_$(1)): V2 := $$(shell cat $$(MAS_$(1)) | wc -c)
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
	@printf '      [ "files" "$$(V1)" ]\n'         >> $$@
	@printf '      [ "bytes" "$$(V2)" ]\n'         >> $$@
	@printf '      [ * ]\n'                        >> $$@
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

$(foreach PKG, $(PACKAGES), $(eval $(call SUMMARY_TEMPLATE,$(PKG))))

tbls: $(TBLS)
