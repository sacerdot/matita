PACKAGE = hmysql
PREDICATES =

INTERFACE_FILES = \
        hSql.mli 
IMPLEMENTATION_FILES = \
        hSqlite3.ml \
        hMysql.ml \
	$(INTERFACE_FILES:%.mli=%.ml)
EXTRA_OBJECTS_TO_INSTALL =
EXTRA_OBJECTS_TO_CLEAN =

include ../../Makefile.defs
include ../Makefile.common
