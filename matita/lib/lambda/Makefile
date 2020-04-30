H    := @

TAGS := all xoa deps top

all:
	$(H)../../matitac.opt .

# xoa ########################################################################

XOA_DIR      := ../../../components/binaries/xoa
XOA          := xoa.native
XOA_CONF     := xoa.conf.xml
XOA_OPTS     := ../../matita.conf.xml $(XOA_CONF)

xoa: $(XOA_CONF)
	@echo "  EXEC $(XOA) $(XOA_CONF)"
	$(H)$(XOA_DIR)/$(XOA) -s $(XOA_OPTS)

# dep input ##################################################################

DEP_INPUT    := .depend
DEP_DIR      := ../../../components/binaries/matitadep
DEP          := matitadep.native
DEP_OPTS     :=

$(DEP_INPUT): MAS = $(shell find $* -name "*.ma")

$(DEP_INPUT): LINE = $(MAS:%=%:include \"\".)

$(DEP_INPUT): REPL = sed -e 's/^\./lambda/'

$(DEP_INPUT): $(MAS) Makefile
	@echo "  GREP include"
	$(H)grep "include \"" $(MAS) | $(REPL) > $(DEP_INPUT)
	$(H)echo "$(LINE)" | sed -e 's/\"\. /\"\.\n/g' | $(REPL) >> $(DEP_INPUT)

# dep ########################################################################

deps: $(DEP_INPUT)
	@echo "  MATITADEP -c"
	$(H)$(DEP_DIR)/$(DEP) -c $(DEP_OPTS) $<

# top ########################################################################

top: $(DEP_INPUT)
	@echo "  MATITADEP -t"
	$(H)$(DEP_DIR)/$(DEP) -t $(DEP_OPTS) $<

##############################################################################

.PHONY: $(TAGS)

.SUFFIXES:
