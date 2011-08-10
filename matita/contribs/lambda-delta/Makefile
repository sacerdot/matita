H       = @
XOA_DIR = ../../../components/binaries/xoa
XOA     = xoa.native

CONF    = Ground-2/xoa.conf.xml
TARGETS = Ground-2/xoa_natation.ma Ground-2/xoa.ma

all: $(TARGETS)

$(TARGETS): $(CONF)
	@echo "  EXEC $(XOA) $(CONF)"
	$(H)MATITA_RT_BASE_DIR=../.. $(XOA_DIR)/$(XOA) $(CONF)
