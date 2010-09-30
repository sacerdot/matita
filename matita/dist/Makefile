MYSQL_FLAGS = --extended_insert --lock-tables=off --no-create-info
DB = -u helm -h mowgli.cs.unibo.it matita
TABLE_CREATOR = ../../components/binaries/table_creator/table_creator
TABLES := $(shell $(TABLE_CREATOR) list all)
MANUAL_DIR = ../help/C
WEB_DIR = ../../../www/matita

all: static_link
clean: static_link_clean
.PHONY: static_link
static_link:
	$(MAKE) -C static_link/
static_link_clean:
	$(MAKE) -C static_link/ clean
dist: matita_stdlib.sql.gz
.PHONY: matita_stdlib.sql
matita_stdlib.sql:
	mysqldump $(MYSQL_FLAGS) $(DB) $(TABLES) > $@
%.gz: %
	gzip -c $< > $@

dist_pre: 
