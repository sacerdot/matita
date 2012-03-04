H       = @
XOA_DIR = ../../../components/binaries/xoa
XOA     = xoa.native

CONF    = Ground_2/xoa.conf.xml
TARGETS = Ground_2/xoa_natation.ma Ground_2/xoa.ma

PACKAGES = Ground_2 Basic_2 Apps_2

all:

# xoa ########################################################################

xoa: $(TARGETS)

$(TARGETS): $(CONF)
	@echo "  EXEC $(XOA) $(CONF)"
	$(H)MATITA_RT_BASE_DIR=../.. $(XOA_DIR)/$(XOA) $(CONF)

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

# sum ########################################################################

tbls: $(PACKAGES:%=etc/ld_%_sum.tbl)

etc/ld_%_sum.tbl: MAS = $(shell find $* -name "*.ma")

%.tbl: C1 = $(shell grep "inductive \|record " $(MAS) | wc -l)
%.tbl: C2 = $(shell grep "definition \|let rec " $(MAS) | wc -l)
%.tbl: C3 = $(shell grep "inductive \|record \|definition \|let rec " $(MAS) | wc -l)
%.tbl: P1 = $(shell grep "theorem " $(MAS) | wc -l)
%.tbl: P2 = $(shell grep "lemma " $(MAS) | wc -l)
%.tbl: P3 = $(shell grep "lemma \|theorem " $(MAS) | wc -l)

etc/ld_%_sum.tbl: $(MAS)
	@mkdir -p etc
	@printf 'Summary for: $*\n'
	@printf 'name "$(basename $(@F))"\n\n'         >  $@
	@printf 'table {\n'                            >> $@
	@printf '   class "grey" [ "category"\n'       >> $@
	@printf '      [ "objects" * ]\n'              >> $@
	@printf '   ]\n'                               >> $@
	@printf '   class "green" [ "propositions"\n'  >> $@
	@printf '      [ "theorems" "$(P1)" * ]\n'     >> $@
	@printf '      [ "lemmas"   "$(P2)" * ]\n'     >> $@
	@printf '      [ "total"    "$(P3)" * ]\n'     >> $@
	@printf '   ]\n'                               >> $@
	@printf '   class "yellow" [ "concepts"\n'     >> $@
	@printf '      [ "declared" "$(C1)" * ]\n'     >> $@
	@printf '      [ "defined"  "$(C2)" * ]\n'     >> $@
	@printf '      [ "total"    "$(C3)" * ]\n'     >> $@
	@printf '   ]\n'                               >> $@
	@printf '}\n\n'                                >> $@
	@printf 'class "component" { 0 }\n\n'          >> $@
	@printf 'class "plane" { 1 } { 3 } { 5 }\n\n'  >> $@
	@printf 'class "number" { 2 } { 4 } { 6 }\n\n' >> $@
