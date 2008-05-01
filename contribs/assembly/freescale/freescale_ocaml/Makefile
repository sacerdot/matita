CC = ocamlopt.opt -w a

all: medium_tests

# base

matita_datatypes_bool:
	$(CC) -c $@.ml

matita_datatypes_compare:
	$(CC) -c $@.ml

matita_datatypes_constructors:
	$(CC) -c $@.ml

matita_higher_order_defs_functions:
	$(CC) -c $@.ml

matita_logic_connectives:
	$(CC) -c $@.ml

matita_logic_equality:
	$(CC) -c $@.ml

matita_nat_nat:
	$(CC) -c $@.ml

matita_nat_minus: matita_nat_nat
	$(CC) -c $@.ml

matita_nat_plus: matita_nat_nat
	$(CC) -c $@.ml

matita_nat_times: matita_nat_plus matita_nat_nat
	$(CC) -c $@.ml

matita_nat_exp: matita_nat_times matita_nat_nat
	$(CC) -c $@.ml

matita_nat_factorial: matita_nat_times matita_nat_nat
	$(CC) -c $@.ml

matita_nat_sigma_and_pi: matita_nat_times matita_nat_plus matita_nat_nat
	$(CC) -c $@.ml

matita_nat_minimization: matita_nat_nat matita_datatypes_bool
	$(CC) -c $@.ml

matita_nat_compare: matita_nat_nat matita_datatypes_compare matita_datatypes_bool
	$(CC) -c $@.ml

matita_nat_div_and_mod: matita_nat_nat matita_nat_minus matita_nat_compare matita_datatypes_constructors matita_datatypes_bool
	$(CC) -c $@.ml

matita_nat_primes: matita_nat_nat matita_nat_minimization matita_nat_div_and_mod matita_nat_compare matita_datatypes_bool
	$(CC) -c $@.ml

matita_list_list: matita_nat_nat
	$(CC) -c $@.ml

# FREESCALE

matita_freescale_extra: matita_nat_nat matita_datatypes_constructors matita_datatypes_bool
	$(CC) -c $@.ml

matita_freescale_exadecim: matita_nat_nat matita_freescale_extra matita_datatypes_constructors matita_datatypes_bool
	$(CC) -c $@.ml

matita_freescale_byte8: matita_nat_times matita_nat_plus matita_nat_nat matita_nat_div_and_mod matita_freescale_extra matita_freescale_exadecim matita_datatypes_constructors matita_datatypes_bool
	$(CC) -c $@.ml

matita_freescale_word16: matita_nat_times matita_nat_plus matita_nat_nat matita_nat_div_and_mod matita_freescale_extra matita_freescale_exadecim matita_freescale_byte8 matita_datatypes_constructors matita_datatypes_bool
	$(CC) -c $@.ml

matita_freescale_aux_bases: matita_freescale_extra matita_freescale_exadecim matita_freescale_byte8
	$(CC) -c $@.ml

matita_freescale_opcode: matita_nat_nat matita_list_list matita_freescale_word16 matita_freescale_extra matita_freescale_exadecim matita_freescale_byte8 matita_freescale_aux_bases matita_datatypes_bool
	$(CC) -c $@.ml

matita_freescale_table_HC05: matita_list_list matita_freescale_opcode matita_freescale_extra matita_freescale_exadecim matita_freescale_byte8 matita_freescale_aux_bases
	$(CC) -c $@.ml

matita_freescale_table_HC08: matita_list_list matita_freescale_word16 matita_freescale_opcode matita_freescale_extra matita_freescale_exadecim matita_freescale_byte8 matita_freescale_aux_bases
	$(CC) -c $@.ml

matita_freescale_table_HCS08: matita_list_list matita_freescale_word16 matita_freescale_opcode matita_freescale_extra matita_freescale_exadecim matita_freescale_byte8 matita_freescale_aux_bases
	$(CC) -c $@.ml

matita_freescale_table_RS08: matita_list_list matita_freescale_opcode matita_freescale_extra matita_freescale_exadecim matita_freescale_byte8 matita_freescale_aux_bases
	$(CC) -c $@.ml

matita_freescale_translation: matita_logic_connectives matita_list_list matita_freescale_word16 matita_freescale_table_RS08 matita_freescale_table_HCS08 matita_freescale_table_HC08 matita_freescale_table_HC05 matita_freescale_opcode matita_freescale_extra matita_freescale_exadecim matita_freescale_byte8 matita_freescale_aux_bases matita_datatypes_constructors matita_datatypes_bool
	$(CC) -c $@.ml

matita_freescale_memory_struct: matita_freescale_exadecim matita_freescale_byte8 matita_freescale_aux_bases matita_datatypes_bool
	$(CC) -c $@.ml

matita_freescale_memory_func: matita_list_list matita_freescale_word16 matita_freescale_memory_struct matita_freescale_exadecim matita_freescale_byte8 matita_freescale_aux_bases matita_datatypes_constructors matita_datatypes_bool
	$(CC) -c $@.ml

matita_freescale_memory_trees: matita_list_list matita_freescale_word16 matita_freescale_memory_struct matita_freescale_exadecim matita_freescale_byte8 matita_freescale_aux_bases matita_datatypes_constructors matita_datatypes_bool
	$(CC) -c $@.ml

matita_freescale_memory_bits: matita_list_list matita_freescale_word16 matita_freescale_memory_trees matita_freescale_memory_struct matita_freescale_extra matita_freescale_exadecim matita_freescale_byte8 matita_freescale_aux_bases matita_datatypes_constructors matita_datatypes_bool
	$(CC) -c $@.ml

matita_freescale_memory_abs: matita_freescale_memory_trees matita_freescale_memory_struct matita_freescale_memory_func matita_freescale_memory_bits matita_freescale_extra matita_datatypes_constructors
	$(CC) -c $@.ml

matita_freescale_status: matita_nat_nat matita_freescale_word16 matita_freescale_opcode matita_freescale_memory_abs matita_freescale_extra matita_freescale_byte8 matita_datatypes_constructors matita_datatypes_bool
	$(CC) -c $@.ml

matita_freescale_model: matita_list_list matita_freescale_word16 matita_freescale_status matita_freescale_opcode matita_freescale_memory_struct matita_freescale_memory_abs matita_freescale_extra matita_freescale_exadecim matita_freescale_byte8 matita_datatypes_constructors matita_datatypes_bool
	$(CC) -c $@.ml

matita_freescale_load_write: matita_nat_nat matita_freescale_word16 matita_freescale_translation matita_freescale_status matita_freescale_opcode matita_freescale_memory_struct matita_freescale_memory_abs matita_freescale_extra matita_freescale_exadecim matita_freescale_byte8 matita_freescale_aux_bases matita_datatypes_constructors matita_datatypes_bool
	$(CC) -c $@.ml

matita_freescale_multivm: matita_nat_nat matita_freescale_word16 matita_freescale_status matita_freescale_opcode matita_freescale_load_write matita_freescale_extra matita_freescale_exadecim matita_freescale_byte8 matita_datatypes_constructors matita_datatypes_bool
	$(CC) -c $@.ml

matita_freescale_medium_tests_tools: matita_nat_nat matita_list_list matita_freescale_word16 matita_freescale_memory_struct matita_freescale_memory_abs matita_freescale_exadecim matita_freescale_byte8
	$(CC) -c $@.ml

matita_freescale_medium_tests_lemmas: matita_nat_nat matita_freescale_word16 matita_freescale_status matita_freescale_opcode matita_freescale_multivm matita_freescale_memory_trees matita_freescale_memory_abs matita_freescale_load_write matita_freescale_exadecim matita_freescale_byte8 matita_datatypes_bool
	$(CC) -c $@.ml

matita_freescale_debug: matita_datatypes_bool matita_datatypes_constructors matita_list_list matita_freescale_exadecim matita_freescale_byte8 matita_freescale_word16
	$(CC) -c $@.ml

matita_freescale_medium_tests: matita_nat_times matita_nat_sigma_and_pi matita_nat_primes matita_nat_plus matita_nat_nat matita_nat_minus matita_nat_minimization matita_nat_factorial matita_nat_exp matita_nat_div_and_mod matita_nat_compare matita_logic_equality matita_logic_connectives matita_list_list matita_higher_order_defs_functions matita_freescale_word16 matita_freescale_translation matita_freescale_table_RS08 matita_freescale_table_HCS08 matita_freescale_table_HC08 matita_freescale_table_HC05 matita_freescale_status matita_freescale_opcode matita_freescale_multivm matita_freescale_model matita_freescale_memory_trees matita_freescale_memory_struct matita_freescale_memory_func matita_freescale_memory_bits matita_freescale_memory_abs matita_freescale_medium_tests_tools matita_freescale_medium_tests_lemmas matita_freescale_load_write matita_freescale_extra matita_freescale_exadecim matita_freescale_byte8 matita_freescale_aux_bases matita_datatypes_constructors matita_datatypes_compare matita_datatypes_bool matita_freescale_debug
	$(CC) -c $@.ml

medium_tests: matita_nat_times matita_nat_sigma_and_pi matita_nat_primes matita_nat_plus matita_nat_nat matita_nat_minus matita_nat_minimization matita_nat_factorial matita_nat_exp matita_nat_div_and_mod matita_nat_compare matita_logic_equality matita_logic_connectives matita_list_list matita_higher_order_defs_functions matita_freescale_word16 matita_freescale_translation matita_freescale_table_RS08 matita_freescale_table_HCS08 matita_freescale_table_HC08 matita_freescale_table_HC05 matita_freescale_status matita_freescale_opcode matita_freescale_multivm matita_freescale_model matita_freescale_memory_trees matita_freescale_memory_struct matita_freescale_memory_func matita_freescale_memory_bits matita_freescale_memory_abs matita_freescale_medium_tests_tools matita_freescale_medium_tests_lemmas matita_freescale_load_write matita_freescale_extra matita_freescale_exadecim matita_freescale_byte8 matita_freescale_aux_bases matita_datatypes_constructors matita_datatypes_compare matita_datatypes_bool matita_freescale_medium_tests matita_freescale_debug
	$(CC) -o $@ matita_datatypes_bool.cmx matita_datatypes_compare.cmx matita_datatypes_constructors.cmx matita_higher_order_defs_functions.cmx matita_logic_connectives.cmx matita_logic_equality.cmx matita_nat_nat.cmx matita_nat_minus.cmx matita_nat_plus.cmx matita_nat_times.cmx matita_nat_exp.cmx matita_nat_factorial.cmx matita_nat_sigma_and_pi.cmx matita_nat_minimization.cmx matita_nat_compare.cmx matita_nat_div_and_mod.cmx matita_nat_primes.cmx matita_list_list.cmx matita_freescale_extra.cmx matita_freescale_exadecim.cmx matita_freescale_byte8.cmx matita_freescale_word16.cmx matita_freescale_aux_bases.cmx matita_freescale_opcode.cmx matita_freescale_table_HC05.cmx matita_freescale_table_HC08.cmx matita_freescale_table_HCS08.cmx matita_freescale_table_RS08.cmx matita_freescale_translation.cmx matita_freescale_memory_struct.cmx matita_freescale_memory_func.cmx matita_freescale_memory_trees.cmx matita_freescale_memory_bits.cmx matita_freescale_memory_abs.cmx matita_freescale_status.cmx matita_freescale_model.cmx matita_freescale_load_write.cmx matita_freescale_multivm.cmx matita_freescale_medium_tests_tools.cmx matita_freescale_medium_tests_lemmas.cmx matita_freescale_debug.cmx matita_freescale_medium_tests.cmx

clean:
	rm -f *.cm[ixo]
	rm -f *.o
