H       = @
XOA_DIR = ../../../components/binaries/xoa
XOA     = xoa.native

CONF    = xoa.conf.xml
TARGETS = xoa_natation.ma xoa.ma

all: $(TARGETS)

$(TARGETS): $(CONF)
	@echo "  EXEC $(XOA) $(CONF)"
	$(H)MATITA_RT_BASE_DIR=../.. $(XOA_DIR)/$(XOA) $(CONF)
