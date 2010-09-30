
# Targets description:
# 	all (default) -> builds hbugs bytecode library hbugs.cma
# 	opt           -> builds hbugs native library hbugs.cmxa
# 	daemons       -> builds hbugs broker and tutors executables
#
# 	start         -> starts up broker and tutors
# 	stop          -> stop broker and tutors
#
# 	broker        -> builds broker executable
# 	tutors        -> builds tutors executables
# 	client        -> builds hbugs client

PACKAGE = hbugs

IMPLEMENTATION_FILES = 			\
	hbugs_misc.ml			\
	hbugs_common.ml			\
	hbugs_id_generator.ml		\
	hbugs_messages.ml		\
	hbugs_client_gui.ml		\
	hbugs_client.ml
INTERFACE_FILES = \
	hbugs_types.mli \
	$(patsubst %.ml, %.mli, $(IMPLEMENTATION_FILES))

include ../../Makefile.defs
include ../Makefile.common
include .tutors.ml
include .generated_tutors.ml

.tutors.ml:
	echo -n "TUTORS_ML = " > $@
	scripts/ls_tutors.ml | xargs >> $@
.generated_tutors.ml:
	echo -n "GENERATED_TUTORS_ML = " > $@
	scripts/ls_tutors.ml -auto | xargs >> $@

TUTORS = $(patsubst %.ml, %, $(TUTORS_ML))
TUTORS_OPT = $(patsubst %, %.opt, $(TUTORS))
GENERATED_TUTORS = $(patsubst %.ml, %, $(GENERATED_TUTORS_ML))

hbugs_client_gui.ml hbugs_client_gui.mli: hbugs_client_gui.glade
	lablgladecc2 $< > hbugs_client_gui.ml
	$(OCAMLC) -i hbugs_client_gui.ml > hbugs_client_gui.mli

clean: clean_mains
.PHONY: clean_mains
clean_mains:
	rm -f $(TUTORS) $(TUTORS_OPT) broker{,.opt} client{,.opt}
distclean: clean
	rm -f $(GENERATED_TUTORS_ML) hbugs_client_gui.ml{,i}
	rm -f .tutors.ml .generated_tutors.ml

MAINS_DEPS =				\
	hbugs_misc.cmo 			\
	hbugs_messages.cmo 		\
	hbugs_id_generator.cmo
TUTOR_DEPS = $(MAINS_DEPS)		\
	hbugs_tutors.cmo
BROKER_DEPS = $(MAINS_DEPS)		\
	hbugs_broker_registry.cmo
CLIENT_DEPS = $(MAINS_DEPS)		\
	hbugs_client_gui.cmo		\
	hbugs_common.cmo		\
	hbugs_client.cmo
TUTOR_DEPS_OPT = $(patsubst %.cmo, %.cmx, $(TUTOR_DEPS))
BROKER_DEPS_OPT = $(patsubst %.cmo, %.cmx, $(BROKER_DEPS))
CLIENT_DEPS_OPT = $(patsubst %.cmo, %.cmx, $(CLIENT_DEPS))
$(GENERATED_TUTORS_ML): scripts/build_tutors.ml data/tutors_index.xml data/hbugs_tutor.TPL.ml
	scripts/build_tutors.ml
hbugs_tutors.cmo: hbugs_tutors.cmi
hbugs_broker_registry.cmo: hbugs_broker_registry.cmi
.PHONY: daemons
daemons: tutors broker
.PHONY: tutors
tutors: all $(TUTORS)
%_tutor: $(TUTOR_DEPS) %_tutor.ml
	$(OCAMLC) -linkpkg -o $@ $^
%_tutor.opt: $(TUTOR_DEPS_OPT) %_tutor.ml
	$(OCAMLOPT) -linkpkg -o $@ $^
broker: $(BROKER_DEPS) broker.ml
	$(OCAMLC) -linkpkg -o $@ $^
broker.opt: $(BROKER_DEPS_OPT) broker.ml
	$(OCAMLOPT) -linkpkg -o $@ $^
client: $(CLIENT_DEPS) client.ml
	$(OCAMLC) -linkpkg -o $@ $^
client.opt: $(CLIENT_DEPS_OPT) client.ml
	$(OCAMLOPT) -linkpkg -o $@ $^

.PHONY: start stop
start:
	scripts/brokerctl.sh start
	scripts/sabba.sh start
stop:
	scripts/brokerctl.sh stop
	scripts/sabba.sh stop

