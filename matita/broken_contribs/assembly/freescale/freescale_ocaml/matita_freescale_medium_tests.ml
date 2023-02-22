let dTest_HCS08_sReverse_source =
(function elems -> (let m = Matita_freescale_opcode.HCS08 in (Matita_freescale_translation.source_to_byte8 m (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.NOP Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHH Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X5))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX0 Matita_freescale_opcode.LDA Matita_freescale_translation.MaIX0) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX0 Matita_freescale_opcode.LDA Matita_freescale_translation.MaIX0) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X6))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX0 Matita_freescale_opcode.STA Matita_freescale_translation.MaIX0) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX0 Matita_freescale_opcode.STA Matita_freescale_translation.MaIX0) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.AIS (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.RTS Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM2 Matita_freescale_opcode.LDHX (Matita_freescale_translation.MaIMM2(elems))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.STHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X4))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BRA (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X2))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.TSX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.ADD (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.ADC (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X4))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.SUB (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX0 Matita_freescale_opcode.STA Matita_freescale_translation.MaIX0) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X3))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.SBC (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX0 Matita_freescale_opcode.LDX Matita_freescale_translation.MaIX0) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULH Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.AIX (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.XF))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.TXA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.ADD (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHH Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.TSX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.STA (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X3))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.ADC (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.LDX (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X3))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULH Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BSR (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XB,Matita_freescale_exadecim.X8))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.AIS (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.TSX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.INC (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BNE (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.INC (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.TSX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X3))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULH Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INHA Matita_freescale_opcode.LSR Matita_freescale_translation.MaINHA) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.TSX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.LDX (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X4))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INHX Matita_freescale_opcode.ROR Matita_freescale_translation.MaINHX) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULH Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.CPHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))))) (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BHI (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XB,Matita_freescale_exadecim.XD)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
;;

let dTest_HCS08_sReverse_status =
(function t -> (function a_op -> (function hX_op -> (function elems -> (function data -> (Matita_freescale_status.set_acc_8_low_reg Matita_freescale_opcode.HCS08 t (Matita_freescale_status.set_z_flag Matita_freescale_opcode.HCS08 t (Matita_freescale_status.setweak_sp_reg Matita_freescale_opcode.HCS08 t (Matita_freescale_status.setweak_indX_16_reg Matita_freescale_opcode.HCS08 t (Matita_freescale_status.set_pc_reg Matita_freescale_opcode.HCS08 t (Matita_freescale_model.start_of_mcu_version (Matita_freescale_model.FamilyHCS08(Matita_freescale_model.MC9S08GB60)) t (Matita_freescale_memory_abs.load_from_source_at t (Matita_freescale_memory_abs.load_from_source_at t (Matita_freescale_memory_abs.zero_memory t) (dTest_HCS08_sReverse_source elems) Matita_freescale_medium_tests_tools.dTest_HCS08_prog) data Matita_freescale_medium_tests_tools.dTest_HCS08_RAM) (Matita_freescale_model.build_memory_type_of_mcu_version (Matita_freescale_model.FamilyHCS08(Matita_freescale_model.MC9S08GB60)) t) (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)) (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)) Matita_datatypes_bool.False Matita_datatypes_bool.False Matita_datatypes_bool.False Matita_datatypes_bool.False Matita_datatypes_bool.False Matita_datatypes_bool.False) (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X8)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XE,Matita_freescale_exadecim.X0))))) hX_op) (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XD)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.XA))))) Matita_datatypes_bool.True) a_op))))))
;;

let sReverseCalc =
(function string -> 
(match (Matita_freescale_multivm.execute Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE (Matita_freescale_multivm.TickOK((dTest_HCS08_sReverse_status Matita_freescale_memory_abs.MEM_TREE (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)) (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XD)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.XB)))) (Matita_freescale_medium_tests_tools.byte8_strlen string) string))) (Matita_nat_plus.plus (Matita_nat_plus.plus (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Matita_nat_times.times (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Matita_freescale_word16.nat_of_word16 (Matita_freescale_medium_tests_tools.byte8_strlen string)))) (Matita_nat_times.times (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O)))))))))) (Matita_nat_div_and_mod.div (Matita_freescale_word16.nat_of_word16 (Matita_freescale_medium_tests_tools.byte8_strlen string)) (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with 
   Matita_freescale_multivm.TickERR(s,_) -> (Matita_datatypes_constructors.None)
 | Matita_freescale_multivm.TickSUSP(s,_) -> (Matita_datatypes_constructors.None)
 | Matita_freescale_multivm.TickOK(s) -> (Matita_datatypes_constructors.Some((Matita_freescale_status.set_mem_desc Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE s (Matita_freescale_memory_abs.load_from_source_at Matita_freescale_memory_abs.MEM_TREE (Matita_freescale_status.get_mem_desc Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE s) Matita_freescale_medium_tests_tools.dTest_zeros (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XD)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))))))))
)
;;

let sReverseCalcAux =
(function string -> 
(match (Matita_freescale_multivm.execute Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE (Matita_freescale_multivm.TickOK((dTest_HCS08_sReverse_status Matita_freescale_memory_abs.MEM_TREE (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)) (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XD)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.XB)))) (Matita_freescale_medium_tests_tools.byte8_strlen string) string)))
(
Matita_freescale_word16.nat_of_word16(Matita_freescale_word16.Mk_word16(
Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X9,Matita_freescale_exadecim.XF),
Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X8,Matita_freescale_exadecim.X9)))

)) with 
   Matita_freescale_multivm.TickERR(s,_) -> (Matita_datatypes_constructors.None)
 | Matita_freescale_multivm.TickSUSP(s,_) -> (Matita_datatypes_constructors.None)
 | Matita_freescale_multivm.TickOK(s) -> (Matita_datatypes_constructors.Some(s)))
)
;;

let sReverseNoCalc =
(function string -> (Matita_datatypes_constructors.Some((Matita_freescale_status.set_pc_reg Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE (dTest_HCS08_sReverse_status Matita_freescale_memory_abs.MEM_TREE (Matita_datatypes_constructors.fst(Matita_freescale_byte8.shr_b8(Matita_freescale_word16.w16h(Matita_freescale_medium_tests_tools.byte8_strlen string)))) (Matita_datatypes_constructors.fst (Matita_freescale_word16.shr_w16 (Matita_freescale_medium_tests_tools.byte8_strlen string))) (Matita_freescale_medium_tests_tools.byte8_strlen string) (Matita_freescale_medium_tests_tools.byte8_reverse string)) (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X9)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.XB))))))))
;;

let dTest_HCS08_cSort_source =
(function elems -> (let m = Matita_freescale_opcode.HCS08 in (Matita_freescale_translation.source_to_byte8 m (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BRA (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XD))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX2 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaIX2((Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INHA Matita_freescale_opcode.ASL Matita_freescale_translation.MaINHA) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INHX Matita_freescale_opcode.CLR Matita_freescale_translation.MaINHX) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INHX Matita_freescale_opcode.ROL Matita_freescale_translation.MaINHX) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.ADD (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.TXA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.ADC (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XD))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULH Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.INC (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BNE (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX0 Matita_freescale_opcode.INC Matita_freescale_translation.MaIX0) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.TSX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.INC (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BNE (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX0 Matita_freescale_opcode.INC Matita_freescale_translation.MaIX0) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM2 Matita_freescale_opcode.CPHX (Matita_freescale_translation.MaIMM2(elems))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BCS (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XD,Matita_freescale_exadecim.XB))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.TSX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.CLR (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX0 Matita_freescale_opcode.CLR Matita_freescale_translation.MaIX0) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BRA (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XE))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.TSX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X3))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX2 Matita_freescale_opcode.STA (Matita_freescale_translation.MaIX2((Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.AIX (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.STHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X3))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.TSX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.LDX (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INHX Matita_freescale_opcode.ASL Matita_freescale_translation.MaINHX) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INHA Matita_freescale_opcode.ROL Matita_freescale_translation.MaINHA) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULH Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX2 Matita_freescale_opcode.LDHX (Matita_freescale_translation.MaIX2((Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XD)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHH Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.AIX (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.XF))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHH Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULH Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X5))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX2 Matita_freescale_opcode.STA (Matita_freescale_translation.MaIX2((Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XD)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX2 Matita_freescale_opcode.STA (Matita_freescale_translation.MaIX2((Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XD)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULH Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM2 Matita_freescale_opcode.CPHX (Matita_freescale_translation.MaIMM2((Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULH Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BNE (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XC,Matita_freescale_exadecim.X8))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.TSX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.INC (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BNE (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX0 Matita_freescale_opcode.INC Matita_freescale_translation.MaIX0) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM2 Matita_freescale_opcode.CPHX (Matita_freescale_translation.MaIMM2((Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BNE (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XC,Matita_freescale_exadecim.X8))))) (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.STOP Matita_freescale_translation.MaINH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
;;

let dTest_HCS08_cSort_status =
(function t -> (function i_op -> (function a_op -> (function hX_op -> (function elems -> (function data -> (Matita_freescale_status.setweak_i_flag Matita_freescale_opcode.HCS08 t (Matita_freescale_status.set_acc_8_low_reg Matita_freescale_opcode.HCS08 t (Matita_freescale_status.set_z_flag Matita_freescale_opcode.HCS08 t (Matita_freescale_status.setweak_sp_reg Matita_freescale_opcode.HCS08 t (Matita_freescale_status.setweak_indX_16_reg Matita_freescale_opcode.HCS08 t (Matita_freescale_status.set_pc_reg Matita_freescale_opcode.HCS08 t (Matita_freescale_model.start_of_mcu_version (Matita_freescale_model.FamilyHCS08(Matita_freescale_model.MC9S08GB60)) t (Matita_freescale_memory_abs.load_from_source_at t (Matita_freescale_memory_abs.load_from_source_at t (Matita_freescale_memory_abs.zero_memory t) (dTest_HCS08_cSort_source elems) Matita_freescale_medium_tests_tools.dTest_HCS08_prog) data Matita_freescale_medium_tests_tools.dTest_HCS08_RAM) (Matita_freescale_model.build_memory_type_of_mcu_version (Matita_freescale_model.FamilyHCS08(Matita_freescale_model.MC9S08GB60)) t) (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)) (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)) Matita_datatypes_bool.False Matita_datatypes_bool.False Matita_datatypes_bool.False Matita_datatypes_bool.False Matita_datatypes_bool.False Matita_datatypes_bool.False) Matita_freescale_medium_tests_tools.dTest_HCS08_prog) hX_op) (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XF)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.XB))))) Matita_datatypes_bool.True) a_op) i_op)))))))
;;

let cSortCalc =
(function string -> 
(match (Matita_freescale_multivm.execute Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE (Matita_freescale_multivm.TickOK((dTest_HCS08_cSort_status Matita_freescale_memory_abs.MEM_TREE Matita_datatypes_bool.True (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)) (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XF)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X4,Matita_freescale_exadecim.XC)))) (Matita_freescale_medium_tests_tools.byte8_strlen string) string))) (Matita_nat_plus.plus (Matita_freescale_word16.nat_of_word16 (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X6,Matita_freescale_exadecim.X4)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X6,Matita_freescale_exadecim.X4))))) (Matita_nat_times.times (Matita_freescale_byte8.nat_of_byte8 (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X9,Matita_freescale_exadecim.X6))) (Matita_freescale_word16.nat_of_word16 (Matita_freescale_medium_tests_tools.byte8_strlen string))))) with 
   Matita_freescale_multivm.TickERR(s,_) -> (Matita_datatypes_constructors.None)
 | Matita_freescale_multivm.TickSUSP(s,_) -> (Matita_datatypes_constructors.Some((Matita_freescale_status.set_mem_desc Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE s (Matita_freescale_memory_abs.load_from_source_at Matita_freescale_memory_abs.MEM_TREE (Matita_freescale_status.get_mem_desc Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE s) Matita_freescale_medium_tests_tools.dTest_zeros (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XD)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))))))))
 | Matita_freescale_multivm.TickOK(s) -> (Matita_datatypes_constructors.None))
)
;;

let cSortNoCalc =
(function string -> (Matita_datatypes_constructors.Some((Matita_freescale_status.set_pc_reg Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE (dTest_HCS08_cSort_status Matita_freescale_memory_abs.MEM_TREE Matita_datatypes_bool.False (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.XF)) (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))) (Matita_freescale_medium_tests_tools.byte8_strlen string) (Matita_freescale_medium_tests_tools.byte8_list_ordering string)) (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X9)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.XC))))))))
;;

let dTest_HCS08_gNum_source =
(function elems -> (let m = Matita_freescale_opcode.HCS08 in (Matita_freescale_translation.source_to_byte8 m (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.AIS (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.X6))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.TSX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.CLR (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X9))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.CLR (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X8))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.CLR (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX0 Matita_freescale_opcode.CLR Matita_freescale_translation.MaIX0) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.CLR (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X3))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.CLR (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM2 Matita_freescale_opcode.JSR (Matita_freescale_translation.MaIMM2((Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X9)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.X1))))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.STHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BRA (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X7,Matita_freescale_exadecim.X2))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BSR (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X7,Matita_freescale_exadecim.XB))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.STHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X3))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BRA (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.XB))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHH Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X5))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM2 Matita_freescale_opcode.JSR (Matita_freescale_translation.MaIMM2((Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XA)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XA))))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.AIS (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM2 Matita_freescale_opcode.CPHX (Matita_freescale_translation.MaIMM2((Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BNE (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XF))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.TSX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X3))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.LDX (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INHA Matita_freescale_opcode.CLR Matita_freescale_translation.MaINHA) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.TSX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHH Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.AIX (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X8))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHH Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X3))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM2 Matita_freescale_opcode.JSR (Matita_freescale_translation.MaIMM2((Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XA)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.XA))))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.TSX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.AIX (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XE))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM2 Matita_freescale_opcode.JSR (Matita_freescale_translation.MaIMM2((Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XA)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X0))))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.AIS (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X6))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_DIR2 Matita_freescale_opcode.STA (Matita_freescale_translation.MaDIR2((Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XC)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.TSX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.INC (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X3))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BNE (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.INC (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.CPHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X3))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BHI (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XB,Matita_freescale_exadecim.XD))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.CPHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X7))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BNE (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XD))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X5))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BNE (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X8))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X9))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.AIX (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.STHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XA))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INHX Matita_freescale_opcode.ASL Matita_freescale_translation.MaINHX) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INHH Matita_freescale_opcode.CLR Matita_freescale_translation.MaINHH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX2 Matita_freescale_opcode.STA (Matita_freescale_translation.MaIX2((Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX2 Matita_freescale_opcode.STA (Matita_freescale_translation.MaIX2((Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.TSX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.INC (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BNE (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX0 Matita_freescale_opcode.INC Matita_freescale_translation.MaIX0) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM2 Matita_freescale_opcode.CPHX (Matita_freescale_translation.MaIMM2(elems))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BCS (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X8,Matita_freescale_exadecim.X6))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.AIS (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XA))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.STOP Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INHX Matita_freescale_opcode.CLR Matita_freescale_translation.MaINHX) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INHH Matita_freescale_opcode.CLR Matita_freescale_translation.MaINHH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.STHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X9))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INHH Matita_freescale_opcode.CLR Matita_freescale_translation.MaINHH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.STHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X7))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INHX Matita_freescale_opcode.INC Matita_freescale_translation.MaINHX) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.RTS Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X3))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX0 Matita_freescale_opcode.LDHX Matita_freescale_translation.MaIX0) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHH Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X7))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X3))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.STA (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.STA (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X0))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX0 Matita_freescale_opcode.LDHX Matita_freescale_translation.MaIX0) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.STHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XE))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X5))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INHX0ADD Matita_freescale_opcode.JMP Matita_freescale_translation.MaINHX0ADD) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHH Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHH Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X6))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHH Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XA))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.STHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X8))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XC))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM2 Matita_freescale_opcode.JMP (Matita_freescale_translation.MaIMM2((Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X9)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.XC))))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.TST (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X4))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BNE (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XA))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.TSX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X7))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.LDX (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X4))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INHH Matita_freescale_opcode.CLR Matita_freescale_translation.MaINHH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.DIV Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.STA (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X4))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X9))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.DIV Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.STA (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X5))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.CLR (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X8))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHH Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.STA (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X9))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.RTS Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INHA Matita_freescale_opcode.CLR Matita_freescale_translation.MaINHA) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.LDX (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X8))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.CLC Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.ROL (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XA))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.ROL (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X9))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.ROL (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X5))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.CMP (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BHI (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XD))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BNE (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X8))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X6))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.CMP (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X9))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.BHI (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X3))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X9))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.SUB (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X6))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.STA (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X9))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.SBC (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X5))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.STA (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.SEC Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INHX_and_IMM1 Matita_freescale_opcode.DBNZ (Matita_freescale_translation.MaINHX_and_IMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XD,Matita_freescale_exadecim.X0))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XA))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INHA Matita_freescale_opcode.ROL Matita_freescale_translation.MaINHA) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.STA (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X6))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X9))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.STA (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XA))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.STA (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X8))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.CLR (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X4))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.RTS Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.TSX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X2))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.ADD (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X5))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.STA (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X2))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.ADC (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X4))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.STA (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X0))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.ADC (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X3))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.STA (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X0))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XF))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.ADC (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.STA (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XF))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.AIS (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XA))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULH Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.RTS Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.AIS (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.XE))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.STHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM2 Matita_freescale_opcode.JSR (Matita_freescale_translation.MaIMM2((Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X9)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X9,Matita_freescale_exadecim.X2))))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.AIS (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDHX (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X3))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.RTS Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM2 Matita_freescale_opcode.JSR (Matita_freescale_translation.MaIMM2((Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X9)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X7,Matita_freescale_exadecim.XC))))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM2 Matita_freescale_opcode.JSR (Matita_freescale_translation.MaIMM2((Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X9)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.XB))))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PSHA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X4))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX0 Matita_freescale_opcode.STA Matita_freescale_translation.MaIX0) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X5))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.STA (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X6))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.STA (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_SP1 Matita_freescale_opcode.LDA (Matita_freescale_translation.MaSP1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X7))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IX1 Matita_freescale_opcode.STA (Matita_freescale_translation.MaIX1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X3))))) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULA Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULH Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INH Matita_freescale_opcode.PULX Matita_freescale_translation.MaINH) (Matita_list_list.append (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_IMM1 Matita_freescale_opcode.AIS (Matita_freescale_translation.MaIMM1((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X4))))) (Matita_freescale_translation.compile m Matita_freescale_opcode.MODE_INHX0ADD Matita_freescale_opcode.JMP Matita_freescale_translation.MaINHX0ADD)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
;;

let dTest_HCS08_gNum_status =
(function t -> (function i_op -> (function a_op -> (function hX_op -> (function pC_op -> (function addr -> (function elems -> (function data -> (Matita_freescale_status.setweak_i_flag Matita_freescale_opcode.HCS08 t (Matita_freescale_status.set_acc_8_low_reg Matita_freescale_opcode.HCS08 t (Matita_freescale_status.set_z_flag Matita_freescale_opcode.HCS08 t (Matita_freescale_status.setweak_sp_reg Matita_freescale_opcode.HCS08 t (Matita_freescale_status.setweak_indX_16_reg Matita_freescale_opcode.HCS08 t (Matita_freescale_status.set_pc_reg Matita_freescale_opcode.HCS08 t (Matita_freescale_model.start_of_mcu_version (Matita_freescale_model.FamilyHCS08(Matita_freescale_model.MC9S08GB60)) t (Matita_freescale_memory_abs.load_from_source_at t (Matita_freescale_memory_abs.load_from_source_at t (Matita_freescale_memory_abs.zero_memory t) (dTest_HCS08_gNum_source elems) addr) data Matita_freescale_medium_tests_tools.dTest_HCS08_RAM) (Matita_freescale_model.build_memory_type_of_mcu_version (Matita_freescale_model.FamilyHCS08(Matita_freescale_model.MC9S08GB60)) t) (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)) (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)) Matita_datatypes_bool.False Matita_datatypes_bool.False Matita_datatypes_bool.False Matita_datatypes_bool.False Matita_datatypes_bool.False Matita_datatypes_bool.False) pC_op) hX_op) (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X6,Matita_freescale_exadecim.XF))))) Matita_datatypes_bool.True) a_op) i_op)))))))))
;;

let dTest_HCS08_gNum_aurei =
(function num -> (Matita_list_list.append 
(match (Matita_freescale_word16.gt_w16 num (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XF)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XC,Matita_freescale_exadecim.X0))))) with 
   Matita_datatypes_bool.True -> (Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X6)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XC)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XF)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XC,Matita_freescale_exadecim.X0)),(Matita_list_list.Nil)))))))))))))))))
 | Matita_datatypes_bool.False -> 
(match (Matita_freescale_word16.gt_w16 num (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.X0))))) with 
   Matita_datatypes_bool.True -> (Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X6)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XC)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Nil)))))))))))))))))
 | Matita_datatypes_bool.False -> 
(match (Matita_freescale_word16.gt_w16 num (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XC))))) with 
   Matita_datatypes_bool.True -> (Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X6)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XC)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Nil)))))))))))))))))
 | Matita_datatypes_bool.False -> 
(match (Matita_freescale_word16.gt_w16 num (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X6))))) with 
   Matita_datatypes_bool.True -> (Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X6)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Nil)))))))))))))))))
 | Matita_datatypes_bool.False -> (Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Nil))))))))))))))))))
)
)
)
 (Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Cons((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_list_list.Nil)))))))))))))))))))))))))))))))))))))))))))))))))))
;;

let dTest_HCS08_gNum_execute1 =
let rec dTest_HCS08_gNum_execute1 = 
(function m -> (function t -> (function s -> (function n -> (function ntot -> 
(match s with 
   Matita_freescale_multivm.TickERR(s',error) -> (Matita_freescale_multivm.TickERR(s',error))
 | Matita_freescale_multivm.TickSUSP(s',susp) -> (Matita_freescale_multivm.TickSUSP(s',susp))
 | Matita_freescale_multivm.TickOK(s') -> 
(match n with 
   Matita_nat_nat.O -> (Matita_freescale_multivm.TickOK(s'))
 | Matita_nat_nat.S(n') -> (dTest_HCS08_gNum_execute1 m t (Matita_freescale_multivm.execute m t (Matita_freescale_multivm.TickOK(s')) (Matita_nat_plus.plus ntot (Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O)))))) n' ntot))
)
))))) in dTest_HCS08_gNum_execute1
;;

let dTest_HCS08_gNum_execute2 =
let rec dTest_HCS08_gNum_execute2 = 
(function m -> (function t -> (function s -> (function n -> (function ntot -> 
(match s with 
   Matita_freescale_multivm.TickERR(s',error) -> (Matita_freescale_multivm.TickERR(s',error))
 | Matita_freescale_multivm.TickSUSP(s',susp) -> (Matita_freescale_multivm.TickSUSP(s',susp))
 | Matita_freescale_multivm.TickOK(s') -> 
(match n with 
   Matita_nat_nat.O -> (Matita_freescale_multivm.TickOK(s'))
 | Matita_nat_nat.S(n') -> (dTest_HCS08_gNum_execute2 m t (dTest_HCS08_gNum_execute1 m t (Matita_freescale_multivm.TickOK(s')) (Matita_nat_plus.plus ntot (Matita_nat_nat.S(Matita_nat_nat.O))) ntot) n' ntot))
)
))))) in dTest_HCS08_gNum_execute2
;;

let dTest_HCS08_gNum_execute3 =
let rec dTest_HCS08_gNum_execute3 = 
(function m -> (function t -> (function s -> (function n -> (function ntot -> 
(match s with 
   Matita_freescale_multivm.TickERR(s',error) -> (Matita_freescale_multivm.TickERR(s',error))
 | Matita_freescale_multivm.TickSUSP(s',susp) -> (Matita_freescale_multivm.TickSUSP(s',susp))
 | Matita_freescale_multivm.TickOK(s') -> 
(match n with 
   Matita_nat_nat.O -> (Matita_freescale_multivm.TickOK(s'))
 | Matita_nat_nat.S(n') -> (dTest_HCS08_gNum_execute3 m t (dTest_HCS08_gNum_execute2 m t (Matita_freescale_multivm.TickOK(s')) ntot ntot) n' ntot))
)
))))) in dTest_HCS08_gNum_execute3
;;

let dTest_HCS08_gNum_execute4 =
(function m -> (function t -> (function s -> (function ntot -> 
(match s with 
   Matita_freescale_multivm.TickERR(s',error) -> (Matita_freescale_multivm.TickERR(s',error))
 | Matita_freescale_multivm.TickSUSP(s',susp) -> (Matita_freescale_multivm.TickSUSP(s',susp))
 | Matita_freescale_multivm.TickOK(s') -> (Matita_freescale_multivm.execute m t (dTest_HCS08_gNum_execute3 m t (Matita_freescale_multivm.TickOK(s')) (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O)))))))))))))))))))))) ntot) (Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
))))
;;

let gNumCalc =
(function num -> 
(match (dTest_HCS08_gNum_execute4 Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE (Matita_freescale_multivm.TickOK((dTest_HCS08_gNum_status Matita_freescale_memory_abs.MEM_TREE Matita_datatypes_bool.True (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)) (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XA)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))) (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X8)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XB,Matita_freescale_exadecim.XE)))) (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X8)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XB,Matita_freescale_exadecim.XE)))) num Matita_freescale_medium_tests_tools.dTest_zeros))) (Matita_freescale_word16.nat_of_word16 num)) with 
   Matita_freescale_multivm.TickERR(s,_) -> (Matita_datatypes_constructors.None)
 | Matita_freescale_multivm.TickSUSP(s,_) -> (Matita_datatypes_constructors.Some((Matita_freescale_status.set_mem_desc Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE s (Matita_freescale_memory_abs.load_from_source_at Matita_freescale_memory_abs.MEM_TREE (Matita_freescale_status.get_mem_desc Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE s) Matita_freescale_medium_tests_tools.dTest_zeros3K (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X2,Matita_freescale_exadecim.X0))))))))
 | Matita_freescale_multivm.TickOK(s) -> (Matita_datatypes_constructors.None))
)
;;

let gNumNoCalc =
(function num -> (Matita_datatypes_constructors.Some((dTest_HCS08_gNum_status Matita_freescale_memory_abs.MEM_TREE Matita_datatypes_bool.False (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)) num (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X9)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X5,Matita_freescale_exadecim.X1)))) (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X8)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XB,Matita_freescale_exadecim.XE)))) num (dTest_HCS08_gNum_aurei num)))))
;;

(* CHANGED: COMPUTE RESULTS *)

print_string("evaluating sReverseCalc32");;
print_newline();;
let sReverseCalc32 =
(sReverseCalc Matita_freescale_medium_tests_tools.dTest_random_32)
;;
print_newline();;
print_newline();;

print_string("evaluating sReverseCalc64");;
print_newline();;
let sReverseCalc64 =
(sReverseCalc Matita_freescale_medium_tests_tools.dTest_random_64)
;;
print_newline();;
print_newline();;

print_string("evaluating sReverseCalc128");;
print_newline();;
let sReverseCalc128 =
(sReverseCalc Matita_freescale_medium_tests_tools.dTest_random_128)
;;
print_newline();;
print_newline();;

print_string("evaluating sReverseCalc256");;
print_newline();;
let sReverseCalc256 =
(sReverseCalc Matita_freescale_medium_tests_tools.dTest_random_256)
;;
print_newline();;
print_newline();;

print_string("evaluating sReverseCalc512");;
print_newline();;
let sReverseCalc512 =
(sReverseCalc Matita_freescale_medium_tests_tools.dTest_random_512)
;;
print_newline();;
print_newline();;

print_string("evaluating sReverseCalc1024");;
print_newline();;
let sReverseCalc1024 =
(sReverseCalc Matita_freescale_medium_tests_tools.dTest_random_1024)
;;
print_newline();;
print_newline();;

print_string("evaluating sReverseCalc2048");;
print_newline();;
let sReverseCalc2048 =
(sReverseCalc Matita_freescale_medium_tests_tools.dTest_random_2048)
;;
print_newline();;
print_newline();;

print_string("evaluating sReverseCalc3072");;
print_newline();;
let sReverseCalc3072 =
(sReverseCalc Matita_freescale_medium_tests_tools.dTest_random_3072)
;;
print_newline();;
print_newline();;

print_string("evaluating sReverseNoCalc...");;
print_newline();;
print_newline();;

let sReverseNoCalc32 =
(sReverseNoCalc Matita_freescale_medium_tests_tools.dTest_random_32)
;;

let sReverseNoCalc64 =
(sReverseNoCalc Matita_freescale_medium_tests_tools.dTest_random_64)
;;

let sReverseNoCalc128 =
(sReverseNoCalc Matita_freescale_medium_tests_tools.dTest_random_128)
;;

let sReverseNoCalc256 =
(sReverseNoCalc Matita_freescale_medium_tests_tools.dTest_random_256)
;;

let sReverseNoCalc512 =
(sReverseNoCalc Matita_freescale_medium_tests_tools.dTest_random_512)
;;

let sReverseNoCalc1024 =
(sReverseNoCalc Matita_freescale_medium_tests_tools.dTest_random_1024)
;;

let sReverseNoCalc2048 =
(sReverseNoCalc Matita_freescale_medium_tests_tools.dTest_random_2048)
;;

let sReverseNoCalc3072 =
(sReverseNoCalc Matita_freescale_medium_tests_tools.dTest_random_3072)
;;
print_newline();;
print_newline();;

print_string("evaluating cSortCalc32");;
print_newline();;
let cSortCalc32 =
(cSortCalc Matita_freescale_medium_tests_tools.dTest_random_32)
;;
print_newline();;
print_newline();;

print_string("evaluating cSortCalc64");;
print_newline();;
let cSortCalc64 =
(cSortCalc Matita_freescale_medium_tests_tools.dTest_random_64)
;;
print_newline();;
print_newline();;

print_string("evaluating cSortCalc128");;
print_newline();;
let cSortCalc128 =
(cSortCalc Matita_freescale_medium_tests_tools.dTest_random_128)
;;
print_newline();;
print_newline();;

print_string("evaluating cSortCalc256");;
print_newline();;
let cSortCalc256 =
(cSortCalc Matita_freescale_medium_tests_tools.dTest_random_256)
;;
print_newline();;
print_newline();;

print_string("evaluating cSortCalc512");;
print_newline();;
let cSortCalc512 =
(cSortCalc Matita_freescale_medium_tests_tools.dTest_random_512)
;;
print_newline();;
print_newline();;

print_string("evaluating cSortCalc1024");;
print_newline();;
let cSortCalc1024 =
(cSortCalc Matita_freescale_medium_tests_tools.dTest_random_1024)
;;
print_newline();;
print_newline();;

print_string("evaluating cSortCalc2048");;
print_newline();;
let cSortCalc2048 =
(cSortCalc Matita_freescale_medium_tests_tools.dTest_random_2048)
;;
print_newline();;
print_newline();;

print_string("evaluating cSortCalc3072");;
print_newline();;
let cSortCalc3072 =
(cSortCalc Matita_freescale_medium_tests_tools.dTest_random_3072)
;;
print_newline();;
print_newline();;

print_string("evaluating cSortNoCalc...");;
print_newline();;
print_newline();;

let cSortNoCalc32 =
(cSortNoCalc Matita_freescale_medium_tests_tools.dTest_random_32)
;;

let cSortNoCalc64 =
(cSortNoCalc Matita_freescale_medium_tests_tools.dTest_random_64)
;;

let cSortNoCalc128 =
(cSortNoCalc Matita_freescale_medium_tests_tools.dTest_random_128)
;;

let cSortNoCalc256 =
(cSortNoCalc Matita_freescale_medium_tests_tools.dTest_random_256)
;;

let cSortNoCalc512 =
(cSortNoCalc Matita_freescale_medium_tests_tools.dTest_random_512)
;;

let cSortNoCalc1024 =
(cSortNoCalc Matita_freescale_medium_tests_tools.dTest_random_1024)
;;

let cSortNoCalc2048 =
(cSortNoCalc Matita_freescale_medium_tests_tools.dTest_random_2048)
;;

let cSortNoCalc3072 =
(cSortNoCalc Matita_freescale_medium_tests_tools.dTest_random_3072)
;;
print_newline();;
print_newline();;

print_string("evaluating gNumCalc1");;
print_newline();;
let gNumCalc1 =
(gNumCalc (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1)))))
;;
print_newline();;
print_newline();;

print_string("evaluating gNumCalc2");;
print_newline();;
let gNumCalc2 =
(gNumCalc (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2)))))
;;
print_newline();;
print_newline();;

print_string("evaluating gNumCalc5");;
print_newline();;
let gNumCalc5 =
(gNumCalc (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X5)))))
;;
print_newline();;
print_newline();;

print_string("evaluating gNumCalc10");;
print_newline();;
let gNumCalc10 =
(gNumCalc (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XA)))))
;;
print_newline();;
print_newline();;

print_string("evaluating gNumCalc20");;
print_newline();;
let gNumCalc20 =
(gNumCalc (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X4)))))
;;
print_newline();;
print_newline();;

print_string("evaluating gNumCalc50");;
print_newline();;
let gNumCalc50 =
(gNumCalc (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X2)))))
;;
print_newline();;
print_newline();;

print_string("evaluating gNumCalc100");;
print_newline();;
let gNumCalc100 =
(gNumCalc (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X6,Matita_freescale_exadecim.X4)))))
;;
print_newline();;
print_newline();;

print_string("evaluating gNumCalc250");;
print_newline();;
let gNumCalc250 =
(gNumCalc (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.XA)))))
;;
print_newline();;
print_newline();;

print_string("evaluating gNumCalc500");;
print_newline();;
let gNumCalc500 =
(gNumCalc (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.X4)))))
;;
print_newline();;
print_newline();;

print_string("evaluating gNumCalc1000");;
print_newline();;
let gNumCalc1000 =
(gNumCalc (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X3)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XE,Matita_freescale_exadecim.X8)))))
;;
print_newline();;
print_newline();;

print_string("evaluating gNumNoCalc...");;
print_newline();;
print_newline();;

let gNumNoCalc1 =
(gNumNoCalc (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1)))))
;;

let gNumNoCalc2 =
(gNumNoCalc (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2)))))
;;

let gNumNoCalc5 =
(gNumNoCalc (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X5)))))
;;

let gNumNoCalc10 =
(gNumNoCalc (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XA)))))
;;

let gNumNoCalc20 =
(gNumNoCalc (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X4)))))
;;

let gNumNoCalc50 =
(gNumNoCalc (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.X2)))))
;;

let gNumNoCalc100 =
(gNumNoCalc (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X6,Matita_freescale_exadecim.X4)))))
;;

let gNumNoCalc250 =
(gNumNoCalc (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.XA)))))
;;

let gNumNoCalc500 =
(gNumNoCalc (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.X4)))))
;;

let gNumNoCalc1000 =
(gNumNoCalc (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X3)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XE,Matita_freescale_exadecim.X8)))))
;;

(* CHANGED: COMPARE RESULTS *)

let medium_tests_show_CPU_RAM = Matita_datatypes_bool.True;;

if sReverseCalc32 = sReverseNoCalc32
then print_string("sReverse32 OK")
else print_string("sReverse32 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE sReverseCalc32 sReverseNoCalc32;;
print_newline();;

if sReverseCalc64 = sReverseNoCalc64
then print_string("sReverse64 OK")
else print_string("sReverse64 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE sReverseCalc64 sReverseNoCalc64;;
print_newline();;

if sReverseCalc128 = sReverseNoCalc128
then print_string("sReverse128 OK")
else print_string("sReverse128 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE sReverseCalc128 sReverseNoCalc128;;
print_newline();;

if sReverseCalc256 = sReverseNoCalc256
then print_string("sReverse256 OK")
else print_string("sReverse256 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE sReverseCalc256 sReverseNoCalc256;;
print_newline();;

if sReverseCalc512 = sReverseNoCalc512
then print_string("sReverse512 OK")
else print_string("sReverse512 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE sReverseCalc512 sReverseNoCalc512;;
print_newline();;

if sReverseCalc1024 = sReverseNoCalc1024
then print_string("sReverse1024 OK")
else print_string("sReverse1024 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE sReverseCalc1024 sReverseNoCalc1024;;
print_newline();;

if sReverseCalc2048 = sReverseNoCalc2048
then print_string("sReverse2048 OK")
else print_string("sReverse2048 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE sReverseCalc2048 sReverseNoCalc2048;;
print_newline();;

if sReverseCalc3072 = sReverseNoCalc3072
then print_string("sReverse3072 OK")
else print_string("sReverse3072 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE sReverseCalc3072 sReverseNoCalc3072;;
print_newline();;

if cSortCalc32 = cSortNoCalc32
then print_string("cSort32 OK")
else print_string("cSort32 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE cSortCalc32 cSortNoCalc32;;
print_newline();;

if cSortCalc64 = cSortNoCalc64
then print_string("cSort64 OK")
else print_string("cSort64 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE cSortCalc64 cSortNoCalc64;;
print_newline();;

if cSortCalc128 = cSortNoCalc128
then print_string("cSort128 OK")
else print_string("cSort128 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE cSortCalc128 cSortNoCalc128;;
print_newline();;

if cSortCalc256 = cSortNoCalc256
then print_string("cSort256 OK")
else print_string("cSort256 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE cSortCalc256 cSortNoCalc256;;
print_newline();;

if cSortCalc512 = cSortNoCalc512
then print_string("cSort512 OK")
else print_string("cSort512 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE cSortCalc512 cSortNoCalc512;;
print_newline();;

if cSortCalc1024 = cSortNoCalc1024
then print_string("cSort1024 OK")
else print_string("cSort1024 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE cSortCalc1024 cSortNoCalc1024;;
print_newline();;

if cSortCalc2048 = cSortNoCalc2048
then print_string("cSort2048 OK")
else print_string("cSort2048 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE cSortCalc2048 cSortNoCalc2048;;
print_newline();;

if cSortCalc3072 = cSortNoCalc3072
then print_string("cSort3072 OK")
else print_string("cSort3072 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE cSortCalc3072 cSortNoCalc3072;;
print_newline();;

if gNumCalc1 = gNumNoCalc1
then print_string("gNum1 OK")
else print_string("gNum1 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE gNumCalc1 gNumCalc1;;
print_newline();;

if gNumCalc2 = gNumNoCalc2
then print_string("gNum2 OK")
else print_string("gNum2 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE gNumCalc2 gNumNoCalc2;;
print_newline();;

if gNumCalc5 = gNumNoCalc5
then print_string("gNum5 OK")
else print_string("gNum5 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE gNumCalc5 gNumNoCalc5;;
print_newline();;

if gNumCalc10 = gNumNoCalc10
then print_string("gNum10 OK")
else print_string("gNum10 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE gNumCalc10 gNumNoCalc10;;
print_newline();;

if gNumCalc20 = gNumNoCalc20
then print_string("gNum20 OK")
else print_string("gNum20 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE gNumCalc20 gNumNoCalc20;;
print_newline();;

if gNumCalc50 = gNumNoCalc50
then print_string("gNum50 OK")
else print_string("gNum50 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE gNumCalc50 gNumNoCalc50;;
print_newline();;

if gNumCalc100 = gNumNoCalc100
then print_string("gNum100 OK")
else print_string("gNum100 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE gNumCalc100 gNumNoCalc100;;
print_newline();;

if gNumCalc250 = gNumNoCalc250
then print_string("gNum250 OK")
else print_string("gNum250 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE gNumCalc250 gNumNoCalc250;;
print_newline();;

if gNumCalc500 = gNumNoCalc500
then print_string("gNum500 OK")
else print_string("gNum500 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE gNumCalc500 gNumNoCalc500;;
print_newline();;

if gNumCalc1000 = gNumNoCalc1000
then print_string("gNum1000 OK")
else print_string("gNum1000 KO");;
print_newline();;
if (medium_tests_show_CPU_RAM = Matita_datatypes_bool.True)
 then Matita_freescale_debug.compare_CPU_RAM Matita_freescale_opcode.HCS08 Matita_freescale_memory_abs.MEM_TREE gNumCalc1000 gNumNoCalc1000;;
print_newline();;
