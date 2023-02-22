let execute_ADC_ADD_aux =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (function setflag -> (function fAMC -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_load Matita_datatypes_bool.True m t s cur_pc i) (function s_M_PC -> 
(match s_M_PC with 
   Matita_freescale_extra.TripleT(s_tmp1,m_op,new_pc) -> (let a_op = (Matita_freescale_status.get_acc_8_low_reg m t s_tmp1) in 
(match (fAMC a_op m_op (Matita_freescale_status.get_c_flag m t s_tmp1)) with 
   Matita_datatypes_constructors.Pair(r_op,carry) -> (let a7 = (Matita_freescale_byte8.mSB_b8 a_op) in (let m7 = (Matita_freescale_byte8.mSB_b8 m_op) in (let r7 = (Matita_freescale_byte8.mSB_b8 r_op) in (let a3 = (Matita_freescale_exadecim.mSB_ex (Matita_freescale_byte8.b8l a_op)) in (let m3 = (Matita_freescale_exadecim.mSB_ex (Matita_freescale_byte8.b8l m_op)) in (let r3 = (Matita_freescale_exadecim.mSB_ex (Matita_freescale_byte8.b8l r_op)) in (let s_tmp2 = 
(match setflag with 
   Matita_datatypes_bool.True -> (Matita_freescale_status.set_acc_8_low_reg m t s_tmp1 r_op)
 | Matita_datatypes_bool.False -> s_tmp1)
 in (let s_tmp3 = (Matita_freescale_status.set_z_flag m t s_tmp2 (Matita_freescale_byte8.eq_b8 r_op (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))) in (let s_tmp4 = (Matita_freescale_status.set_c_flag m t s_tmp3 (Matita_freescale_extra.or_bool (Matita_freescale_extra.or_bool (Matita_freescale_extra.and_bool a7 m7) (Matita_freescale_extra.and_bool m7 (Matita_freescale_extra.not_bool r7))) (Matita_freescale_extra.and_bool (Matita_freescale_extra.not_bool r7) a7))) in (let s_tmp5 = (Matita_freescale_status.setweak_n_flag m t s_tmp4 r7) in (let s_tmp6 = (Matita_freescale_status.setweak_h_flag m t s_tmp5 (Matita_freescale_extra.or_bool (Matita_freescale_extra.or_bool (Matita_freescale_extra.and_bool a3 m3) (Matita_freescale_extra.and_bool m3 (Matita_freescale_extra.not_bool r3))) (Matita_freescale_extra.and_bool (Matita_freescale_extra.not_bool r3) a3))) in (let s_tmp7 = (Matita_freescale_status.setweak_v_flag m t s_tmp6 (Matita_freescale_extra.or_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool a7 m7) (Matita_freescale_extra.not_bool r7)) (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.not_bool a7) (Matita_freescale_extra.not_bool m7)) r7))) in (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp7,new_pc)))))))))))))))))
))
)))))))))
;;

let execute_AND_BIT_EOR_ORA_aux =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (function setflag -> (function fAM -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_load Matita_datatypes_bool.True m t s cur_pc i) (function s_M_PC -> 
(match s_M_PC with 
   Matita_freescale_extra.TripleT(s_tmp1,m_op,new_pc) -> (let r_op = (fAM (Matita_freescale_status.get_acc_8_low_reg m t s_tmp1) m_op) in (let s_tmp2 = 
(match setflag with 
   Matita_datatypes_bool.True -> (Matita_freescale_status.set_acc_8_low_reg m t s_tmp1 r_op)
 | Matita_datatypes_bool.False -> s_tmp1)
 in (let s_tmp3 = (Matita_freescale_status.set_z_flag m t s_tmp2 (Matita_freescale_byte8.eq_b8 r_op (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))) in (let s_tmp4 = (Matita_freescale_status.setweak_n_flag m t s_tmp3 (Matita_freescale_byte8.mSB_b8 r_op)) in (let s_tmp5 = (Matita_freescale_status.setweak_v_flag m t s_tmp4 Matita_datatypes_bool.False) in (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp5,new_pc))))))))))
)))))))))
;;

let execute_ASL_ASR_LSR_ROL_ROR_aux =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (function fMC -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_load Matita_datatypes_bool.True m t s cur_pc i) (function s_M_PC -> 
(match s_M_PC with 
   Matita_freescale_extra.TripleT(s_tmp1,m_op,_) -> 
(match (fMC m_op (Matita_freescale_status.get_c_flag m t s_tmp1)) with 
   Matita_datatypes_constructors.Pair(r_op,carry) -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_write Matita_datatypes_bool.True m t s_tmp1 cur_pc i r_op) (function s_PC -> 
(match s_PC with 
   Matita_datatypes_constructors.Pair(s_tmp2,new_pc) -> (let s_tmp3 = (Matita_freescale_status.set_c_flag m t s_tmp2 carry) in (let s_tmp4 = (Matita_freescale_status.set_z_flag m t s_tmp3 (Matita_freescale_byte8.eq_b8 r_op (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))) in (let s_tmp5 = (Matita_freescale_status.setweak_n_flag m t s_tmp4 (Matita_freescale_byte8.mSB_b8 r_op)) in (let s_tmp6 = (Matita_freescale_status.setweak_v_flag m t s_tmp5 (Matita_freescale_extra.xor_bool (Matita_freescale_byte8.mSB_b8 r_op) carry)) in (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp6,new_pc)))))))))
)))
)
))))))))
;;

let byte_extension =
(function b -> (Matita_freescale_word16.Mk_word16(
(match (Matita_freescale_byte8.mSB_b8 b) with 
   Matita_datatypes_bool.True -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.XF))
 | Matita_datatypes_bool.False -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))
,b)))
;;

let branched_pc =
(function m -> (function t -> (function s -> (function cur_pc -> (function b -> (Matita_freescale_status.get_pc_reg m t (Matita_freescale_status.set_pc_reg m t s (Matita_freescale_word16.plus_w16nc cur_pc (byte_extension b)))))))))
;;

let execute_any_BRANCH =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (function fCOND -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_load Matita_datatypes_bool.True m t s cur_pc i) (function s_M_PC -> 
(match s_M_PC with 
   Matita_freescale_extra.TripleT(s_tmp1,m_op,new_pc) -> 
(match fCOND with 
   Matita_datatypes_bool.True -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp1,(branched_pc m t s_tmp1 new_pc m_op)))))
 | Matita_datatypes_bool.False -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp1,new_pc)))))
)
))))))))
;;

let execute_BCLRn_BSETn_aux =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (function optval -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_write Matita_datatypes_bool.True m t s cur_pc i optval) (function s_PC -> 
(match s_PC with 
   Matita_datatypes_constructors.Pair(s_tmp1,new_pc) -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp1,new_pc)))))
))))))))
;;

let execute_BRCLRn_BRSETn_aux =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (function fCOND -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_load Matita_datatypes_bool.False m t s cur_pc i) (function s_M_PC -> 
(match s_M_PC with 
   Matita_freescale_extra.TripleT(s_tmp1,m_op,new_pc) -> 
(match m_op with 
   Matita_freescale_word16.Mk_word16(mH_op,mL_op) -> 
(match (fCOND mH_op) with 
   Matita_datatypes_bool.True -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp1,(branched_pc m t s_tmp1 new_pc mL_op)))))
 | Matita_datatypes_bool.False -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp1,new_pc)))))
)
)
))))))))
;;

let execute_COM_DEC_INC_NEG_aux =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (function fM -> (function fV -> (function fC -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_load Matita_datatypes_bool.True m t s cur_pc i) (function s_M_PC -> 
(match s_M_PC with 
   Matita_freescale_extra.TripleT(s_tmp1,m_op,_) -> (let r_op = (fM m_op) in (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_write Matita_datatypes_bool.True m t s_tmp1 cur_pc i r_op) (function s_PC -> 
(match s_PC with 
   Matita_datatypes_constructors.Pair(s_tmp2,new_pc) -> (let s_tmp3 = (Matita_freescale_status.set_c_flag m t s_tmp2 (fC (Matita_freescale_status.get_c_flag m t s_tmp2) r_op)) in (let s_tmp4 = (Matita_freescale_status.set_z_flag m t s_tmp3 (Matita_freescale_byte8.eq_b8 r_op (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))) in (let s_tmp5 = (Matita_freescale_status.setweak_n_flag m t s_tmp4 (Matita_freescale_byte8.mSB_b8 r_op)) in (let s_tmp6 = (Matita_freescale_status.setweak_v_flag m t s_tmp5 (fV (Matita_freescale_byte8.mSB_b8 m_op) (Matita_freescale_byte8.mSB_b8 r_op))) in (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp6,new_pc)))))))))
))))
))))))))))
;;

let execute_SBC_SUB_aux =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (function setflag -> (function fAMC -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_load Matita_datatypes_bool.True m t s cur_pc i) (function s_M_PC -> 
(match s_M_PC with 
   Matita_freescale_extra.TripleT(s_tmp1,m_op,new_pc) -> (let a_op = (Matita_freescale_status.get_acc_8_low_reg m t s_tmp1) in 
(match (fAMC a_op m_op (Matita_freescale_status.get_c_flag m t s_tmp1)) with 
   Matita_datatypes_constructors.Pair(r_op,carry) -> (let a7 = (Matita_freescale_byte8.mSB_b8 a_op) in (let m7 = (Matita_freescale_byte8.mSB_b8 m_op) in (let r7 = (Matita_freescale_byte8.mSB_b8 r_op) in (let s_tmp2 = 
(match setflag with 
   Matita_datatypes_bool.True -> (Matita_freescale_status.set_acc_8_low_reg m t s_tmp1 r_op)
 | Matita_datatypes_bool.False -> s_tmp1)
 in (let s_tmp3 = (Matita_freescale_status.set_z_flag m t s_tmp2 (Matita_freescale_byte8.eq_b8 r_op (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))) in (let s_tmp4 = (Matita_freescale_status.set_c_flag m t s_tmp3 (Matita_freescale_extra.or_bool (Matita_freescale_extra.or_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.not_bool a7) m7) (Matita_freescale_extra.and_bool m7 r7)) (Matita_freescale_extra.and_bool r7 (Matita_freescale_extra.not_bool a7)))) in (let s_tmp5 = (Matita_freescale_status.setweak_n_flag m t s_tmp4 r7) in (let s_tmp6 = (Matita_freescale_status.setweak_v_flag m t s_tmp5 (Matita_freescale_extra.or_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool a7 (Matita_freescale_extra.not_bool m7)) (Matita_freescale_extra.not_bool r7)) (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.not_bool a7) m7) r7))) in (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp6,new_pc)))))))))))))
))
)))))))))
;;

let aux_push =
(function m -> (function t -> (function s -> (function val_ -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_sp_reg m t s) (function sP_op -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.memory_filter_write m t s sP_op val_) (function s_tmp1 -> (Matita_freescale_extra.opt_map (Matita_freescale_status.set_sp_reg m t s_tmp1 (Matita_freescale_word16.pred_w16 sP_op)) (function s_tmp2 -> (Matita_datatypes_constructors.Some(s_tmp2))))))))))))
;;

let aux_pop =
(function m -> (function t -> (function s -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_sp_reg m t s) (function sP_op -> (Matita_freescale_extra.opt_map (Matita_freescale_status.set_sp_reg m t s (Matita_freescale_word16.succ_w16 sP_op)) (function s_tmp1 -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_sp_reg m t s_tmp1) (function sP_op' -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.memory_filter_read m t s_tmp1 sP_op') (function val_ -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp1,val_)))))))))))))))
;;

let aux_get_CCR =
(function m -> (function t -> (function s -> (let v_comp = 
(match (Matita_freescale_status.get_v_flag m t s) with 
   Matita_datatypes_constructors.None -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X8,Matita_freescale_exadecim.X0))
 | Matita_datatypes_constructors.Some(v_val) -> 
(match v_val with 
   Matita_datatypes_bool.True -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X8,Matita_freescale_exadecim.X0))
 | Matita_datatypes_bool.False -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))
)
 in (let h_comp = 
(match (Matita_freescale_status.get_h_flag m t s) with 
   Matita_datatypes_constructors.None -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X0))
 | Matita_datatypes_constructors.Some(h_val) -> 
(match h_val with 
   Matita_datatypes_bool.True -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X0))
 | Matita_datatypes_bool.False -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))
)
 in (let i_comp = 
(match (Matita_freescale_status.get_i_flag m t s) with 
   Matita_datatypes_constructors.None -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X8))
 | Matita_datatypes_constructors.Some(i_val) -> 
(match i_val with 
   Matita_datatypes_bool.True -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X8))
 | Matita_datatypes_bool.False -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))
)
 in (let n_comp = 
(match (Matita_freescale_status.get_n_flag m t s) with 
   Matita_datatypes_constructors.None -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X4))
 | Matita_datatypes_constructors.Some(n_val) -> 
(match n_val with 
   Matita_datatypes_bool.True -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X4))
 | Matita_datatypes_bool.False -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))
)
 in (let z_comp = 
(match (Matita_freescale_status.get_z_flag m t s) with 
   Matita_datatypes_bool.True -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2))
 | Matita_datatypes_bool.False -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))
 in (let c_comp = 
(match (Matita_freescale_status.get_c_flag m t s) with 
   Matita_datatypes_bool.True -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))
 | Matita_datatypes_bool.False -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))
 in (Matita_freescale_byte8.or_b8 (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X6,Matita_freescale_exadecim.X0)) (Matita_freescale_byte8.or_b8 v_comp (Matita_freescale_byte8.or_b8 h_comp (Matita_freescale_byte8.or_b8 i_comp (Matita_freescale_byte8.or_b8 n_comp (Matita_freescale_byte8.or_b8 z_comp c_comp)))))))))))))))
;;

let aux_set_CCR =
(function m -> (function t -> (function s -> (function cCR -> (let s_tmp1 = (Matita_freescale_status.set_c_flag m t s (Matita_freescale_byte8.eq_b8 (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1)) (Matita_freescale_byte8.and_b8 (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1)) cCR))) in (let s_tmp2 = (Matita_freescale_status.set_z_flag m t s_tmp1 (Matita_freescale_byte8.eq_b8 (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2)) (Matita_freescale_byte8.and_b8 (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X2)) cCR))) in (let s_tmp3 = (Matita_freescale_status.setweak_n_flag m t s_tmp2 (Matita_freescale_byte8.eq_b8 (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X4)) (Matita_freescale_byte8.and_b8 (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X4)) cCR))) in (let s_tmp4 = (Matita_freescale_status.setweak_i_flag m t s_tmp3 (Matita_freescale_byte8.eq_b8 (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X8)) (Matita_freescale_byte8.and_b8 (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X8)) cCR))) in (let s_tmp5 = (Matita_freescale_status.setweak_h_flag m t s_tmp4 (Matita_freescale_byte8.eq_b8 (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X0)) (Matita_freescale_byte8.and_b8 (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.X0)) cCR))) in (let s_tmp6 = (Matita_freescale_status.setweak_v_flag m t s_tmp5 (Matita_freescale_byte8.eq_b8 (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X8,Matita_freescale_exadecim.X0)) (Matita_freescale_byte8.and_b8 (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X8,Matita_freescale_exadecim.X0)) cCR))) in s_tmp6))))))))))
;;

let execute_ADC =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_ADC_ADD_aux m t s i cur_pc Matita_datatypes_bool.True (function a_op -> (function m_op -> (function c_op -> (Matita_freescale_byte8.plus_b8 a_op m_op c_op))))))))))
;;

let execute_ADD =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_ADC_ADD_aux m t s i cur_pc Matita_datatypes_bool.True (function a_op -> (function m_op -> (function c_op -> (Matita_freescale_byte8.plus_b8 a_op m_op Matita_datatypes_bool.False))))))))))
;;

let execute_AIS =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_load Matita_datatypes_bool.True m t s cur_pc i) (function s_M_PC -> 
(match s_M_PC with 
   Matita_freescale_extra.TripleT(s_tmp1,m_op,new_pc) -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_sp_reg m t s_tmp1) (function sP_op -> (Matita_freescale_extra.opt_map (Matita_freescale_status.set_sp_reg m t s_tmp1 (Matita_freescale_word16.plus_w16nc sP_op (byte_extension m_op))) (function s_tmp2 -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp2,new_pc)))))))))
)))))))
;;

let execute_AIX =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_load Matita_datatypes_bool.True m t s cur_pc i) (function s_M_PC -> 
(match s_M_PC with 
   Matita_freescale_extra.TripleT(s_tmp1,m_op,new_pc) -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_indX_16_reg m t s_tmp1) (function hX_op -> (Matita_freescale_extra.opt_map (Matita_freescale_status.set_indX_16_reg m t s_tmp1 (Matita_freescale_word16.plus_w16nc hX_op (byte_extension m_op))) (function s_tmp2 -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp2,new_pc)))))))))
)))))))
;;

let execute_AND =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_AND_BIT_EOR_ORA_aux m t s i cur_pc Matita_datatypes_bool.True Matita_freescale_byte8.and_b8))))))
;;

let execute_ASL =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_ASL_ASR_LSR_ROL_ROR_aux m t s i cur_pc (function m_op -> (function c_op -> (Matita_freescale_byte8.rcl_b8 m_op Matita_datatypes_bool.False)))))))))
;;

let execute_ASR =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_ASL_ASR_LSR_ROL_ROR_aux m t s i cur_pc (function m_op -> (function c_op -> (Matita_freescale_byte8.rcr_b8 m_op (Matita_freescale_byte8.mSB_b8 m_op))))))))))
;;

let execute_BCC =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_any_BRANCH m t s i cur_pc (Matita_freescale_extra.not_bool (Matita_freescale_status.get_c_flag m t s))))))))
;;

let execute_BCLRn =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_BCLRn_BSETn_aux m t s i cur_pc (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))))))))
;;

let execute_BCS =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_any_BRANCH m t s i cur_pc (Matita_freescale_status.get_c_flag m t s)))))))
;;

let execute_BEQ =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_any_BRANCH m t s i cur_pc (Matita_freescale_status.get_z_flag m t s)))))))
;;

let execute_BGE =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_n_flag m t s) (function n_op -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_v_flag m t s) (function v_op -> (execute_any_BRANCH m t s i cur_pc (Matita_freescale_extra.not_bool (Matita_freescale_extra.xor_bool n_op v_op))))))))))))
;;

let execute_BGND =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s,cur_pc)))))))))
;;

let execute_BGT =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_n_flag m t s) (function n_op -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_v_flag m t s) (function v_op -> (execute_any_BRANCH m t s i cur_pc (Matita_freescale_extra.not_bool (Matita_freescale_extra.or_bool (Matita_freescale_status.get_z_flag m t s) (Matita_freescale_extra.xor_bool n_op v_op)))))))))))))
;;

let execute_BHCC =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_h_flag m t s) (function h_op -> (execute_any_BRANCH m t s i cur_pc (Matita_freescale_extra.not_bool h_op)))))))))
;;

let execute_BHCS =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_h_flag m t s) (function h_op -> (execute_any_BRANCH m t s i cur_pc h_op))))))))
;;

let execute_BHI =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_any_BRANCH m t s i cur_pc (Matita_freescale_extra.not_bool (Matita_freescale_extra.or_bool (Matita_freescale_status.get_c_flag m t s) (Matita_freescale_status.get_z_flag m t s)))))))))
;;

let execute_BIH =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_irq_flag m t s) (function iRQ_op -> (execute_any_BRANCH m t s i cur_pc (Matita_freescale_extra.not_bool iRQ_op)))))))))
;;

let execute_BIL =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_irq_flag m t s) (function iRQ_op -> (execute_any_BRANCH m t s i cur_pc iRQ_op))))))))
;;

let execute_BIT =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_AND_BIT_EOR_ORA_aux m t s i cur_pc Matita_datatypes_bool.False Matita_freescale_byte8.and_b8))))))
;;

let execute_BLE =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_n_flag m t s) (function n_op -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_v_flag m t s) (function v_op -> (execute_any_BRANCH m t s i cur_pc (Matita_freescale_extra.or_bool (Matita_freescale_status.get_z_flag m t s) (Matita_freescale_extra.xor_bool n_op v_op))))))))))))
;;

let execute_BLS =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_any_BRANCH m t s i cur_pc (Matita_freescale_extra.or_bool (Matita_freescale_status.get_c_flag m t s) (Matita_freescale_status.get_z_flag m t s))))))))
;;

let execute_BLT =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_n_flag m t s) (function n_op -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_v_flag m t s) (function v_op -> (execute_any_BRANCH m t s i cur_pc (Matita_freescale_extra.xor_bool n_op v_op)))))))))))
;;

let execute_BMC =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_i_flag m t s) (function i_op -> (execute_any_BRANCH m t s i cur_pc (Matita_freescale_extra.not_bool i_op)))))))))
;;

let execute_BMI =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_n_flag m t s) (function n_op -> (execute_any_BRANCH m t s i cur_pc n_op))))))))
;;

let execute_BMS =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_i_flag m t s) (function i_op -> (execute_any_BRANCH m t s i cur_pc i_op))))))))
;;

let execute_BNE =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_any_BRANCH m t s i cur_pc (Matita_freescale_extra.not_bool (Matita_freescale_status.get_z_flag m t s))))))))
;;

let execute_BPL =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_n_flag m t s) (function n_op -> (execute_any_BRANCH m t s i cur_pc (Matita_freescale_extra.not_bool n_op)))))))))
;;

let execute_BRA =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_any_BRANCH m t s i cur_pc Matita_datatypes_bool.True))))))
;;

let execute_BRCLRn =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_BRCLRn_BRSETn_aux m t s i cur_pc (function mn_op -> (Matita_freescale_byte8.eq_b8 mn_op (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))))))))))
;;

let execute_BRN =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_any_BRANCH m t s i cur_pc Matita_datatypes_bool.False))))))
;;

let execute_BRSETn =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_BRCLRn_BRSETn_aux m t s i cur_pc (function mn_op -> (Matita_freescale_extra.not_bool (Matita_freescale_byte8.eq_b8 mn_op (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))))))))))
;;

let execute_BSETn =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_BCLRn_BSETn_aux m t s i cur_pc (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.XF))))))))
;;

let execute_BSR =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_load Matita_datatypes_bool.True m t s cur_pc i) (function s_M_PC -> 
(match s_M_PC with 
   Matita_freescale_extra.TripleT(s_tmp1,m_op,new_pc) -> (let aux = (Matita_freescale_extra.opt_map (aux_push m t s_tmp1 (Matita_freescale_word16.w16l new_pc)) (function s_tmp2 -> (Matita_freescale_extra.opt_map (aux_push m t s_tmp2 (Matita_freescale_word16.w16h new_pc)) (function s_tmp3 -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp3,(branched_pc m t s_tmp3 new_pc m_op))))))))) in 
(match m with 
   Matita_freescale_opcode.HC05 -> aux
 | Matita_freescale_opcode.HC08 -> aux
 | Matita_freescale_opcode.HCS08 -> aux
 | Matita_freescale_opcode.RS08 -> (Matita_freescale_extra.opt_map (Matita_freescale_status.set_spc_reg m t s_tmp1 new_pc) (function s_tmp2 -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp2,(branched_pc m t s_tmp2 new_pc m_op))))))))
))
)))))))
;;

let execute_CBEQA =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_load Matita_datatypes_bool.False m t s cur_pc i) (function s_M_PC -> 
(match s_M_PC with 
   Matita_freescale_extra.TripleT(s_tmp1,m_op,new_pc) -> 
(match m_op with 
   Matita_freescale_word16.Mk_word16(mH_op,mL_op) -> 
(match (Matita_freescale_byte8.eq_b8 (Matita_freescale_status.get_acc_8_low_reg m t s_tmp1) mH_op) with 
   Matita_datatypes_bool.True -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp1,(branched_pc m t s_tmp1 new_pc mL_op)))))
 | Matita_datatypes_bool.False -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp1,new_pc)))))
)
)
)))))))
;;

let execute_CBEQX =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_load Matita_datatypes_bool.False m t s cur_pc i) (function s_M_PC -> 
(match s_M_PC with 
   Matita_freescale_extra.TripleT(s_tmp1,m_op,new_pc) -> 
(match m_op with 
   Matita_freescale_word16.Mk_word16(mH_op,mL_op) -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_indX_8_low_reg m t s_tmp1) (function x_op -> 
(match (Matita_freescale_byte8.eq_b8 x_op mH_op) with 
   Matita_datatypes_bool.True -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp1,(branched_pc m t s_tmp1 new_pc mL_op)))))
 | Matita_datatypes_bool.False -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp1,new_pc)))))
)))
)
)))))))
;;

let execute_CLC =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair((Matita_freescale_status.set_c_flag m t s Matita_datatypes_bool.False),cur_pc)))))))))
;;

let execute_CLI =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.set_i_flag m t s Matita_datatypes_bool.False) (function s_tmp -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp,cur_pc)))))))))))
;;

let execute_CLR =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_write Matita_datatypes_bool.True m t s cur_pc i (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))) (function s_PC -> 
(match s_PC with 
   Matita_datatypes_constructors.Pair(s_tmp1,new_pc) -> (let s_tmp2 = (Matita_freescale_status.set_z_flag m t s_tmp1 Matita_datatypes_bool.True) in (let s_tmp3 = (Matita_freescale_status.setweak_n_flag m t s_tmp2 Matita_datatypes_bool.False) in (let s_tmp4 = (Matita_freescale_status.setweak_v_flag m t s_tmp3 Matita_datatypes_bool.False) in (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp4,new_pc))))))))
)))))))
;;

let execute_CMP =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_SBC_SUB_aux m t s i cur_pc Matita_datatypes_bool.False (function a_op -> (function m_op -> (function c_op -> (Matita_freescale_byte8.plus_b8 a_op (Matita_freescale_byte8.compl_b8 m_op) Matita_datatypes_bool.False))))))))))
;;

let execute_COM =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_COM_DEC_INC_NEG_aux m t s i cur_pc Matita_freescale_byte8.not_b8 (function m7 -> (function r7 -> Matita_datatypes_bool.False)) (function c_op -> (function r_op -> Matita_datatypes_bool.True))))))))
;;

let execute_CPHX =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_load Matita_datatypes_bool.False m t s cur_pc i) (function s_M_PC -> 
(match s_M_PC with 
   Matita_freescale_extra.TripleT(s_tmp1,m_op,new_pc) -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_indX_16_reg m t s_tmp1) (function x_op -> 
(match (Matita_freescale_word16.plus_w16 x_op (Matita_freescale_word16.compl_w16 m_op) Matita_datatypes_bool.False) with 
   Matita_datatypes_constructors.Pair(r_op,carry) -> (let x15 = (Matita_freescale_word16.mSB_w16 x_op) in (let m15 = (Matita_freescale_word16.mSB_w16 m_op) in (let r15 = (Matita_freescale_word16.mSB_w16 r_op) in (let s_tmp2 = (Matita_freescale_status.set_z_flag m t s_tmp1 (Matita_freescale_word16.eq_w16 r_op (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))))) in (let s_tmp3 = (Matita_freescale_status.set_c_flag m t s_tmp2 (Matita_freescale_extra.or_bool (Matita_freescale_extra.or_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.not_bool x15) m15) (Matita_freescale_extra.and_bool m15 r15)) (Matita_freescale_extra.and_bool r15 (Matita_freescale_extra.not_bool x15)))) in (let s_tmp4 = (Matita_freescale_status.setweak_n_flag m t s_tmp3 r15) in (let s_tmp5 = (Matita_freescale_status.setweak_v_flag m t s_tmp4 (Matita_freescale_extra.or_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool x15 (Matita_freescale_extra.not_bool m15)) (Matita_freescale_extra.not_bool r15)) (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.not_bool x15) m15) r15))) in (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp5,new_pc))))))))))))
)))
)))))))
;;

let execute_CPX =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_load Matita_datatypes_bool.True m t s cur_pc i) (function s_M_PC -> 
(match s_M_PC with 
   Matita_freescale_extra.TripleT(s_tmp1,m_op,new_pc) -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_indX_8_low_reg m t s_tmp1) (function x_op -> 
(match (Matita_freescale_byte8.plus_b8 x_op (Matita_freescale_byte8.compl_b8 m_op) Matita_datatypes_bool.False) with 
   Matita_datatypes_constructors.Pair(r_op,carry) -> (let x7 = (Matita_freescale_byte8.mSB_b8 x_op) in (let m7 = (Matita_freescale_byte8.mSB_b8 m_op) in (let r7 = (Matita_freescale_byte8.mSB_b8 r_op) in (let s_tmp2 = (Matita_freescale_status.set_z_flag m t s_tmp1 (Matita_freescale_byte8.eq_b8 r_op (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))) in (let s_tmp3 = (Matita_freescale_status.set_c_flag m t s_tmp2 (Matita_freescale_extra.or_bool (Matita_freescale_extra.or_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.not_bool x7) m7) (Matita_freescale_extra.and_bool m7 r7)) (Matita_freescale_extra.and_bool r7 (Matita_freescale_extra.not_bool x7)))) in (let s_tmp4 = (Matita_freescale_status.setweak_n_flag m t s_tmp3 r7) in (let s_tmp5 = (Matita_freescale_status.setweak_v_flag m t s_tmp4 (Matita_freescale_extra.or_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool x7 (Matita_freescale_extra.not_bool m7)) (Matita_freescale_extra.not_bool r7)) (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.not_bool x7) m7) r7))) in (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp5,new_pc))))))))))))
)))
)))))))
;;

let execute_DAA =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_h_flag m t s) (function h -> (let m_op = (Matita_freescale_status.get_acc_8_low_reg m t s) in 
(match (Matita_freescale_byte8.daa_b8 h (Matita_freescale_status.get_c_flag m t s) m_op) with 
   Matita_datatypes_constructors.Pair(r_op,carry) -> (let s_tmp1 = (Matita_freescale_status.set_acc_8_low_reg m t s r_op) in (let s_tmp2 = (Matita_freescale_status.set_z_flag m t s_tmp1 (Matita_freescale_byte8.eq_b8 r_op (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))) in (let s_tmp3 = (Matita_freescale_status.set_c_flag m t s_tmp2 carry) in (let s_tmp4 = (Matita_freescale_status.setweak_n_flag m t s_tmp3 (Matita_freescale_byte8.mSB_b8 r_op)) in (let s_tmp5 = (Matita_freescale_status.setweak_v_flag m t s_tmp4 (Matita_freescale_extra.xor_bool (Matita_freescale_byte8.mSB_b8 m_op) (Matita_freescale_byte8.mSB_b8 r_op))) in (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp5,cur_pc))))))))))
))))))))
;;

let execute_DBNZ =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_load Matita_datatypes_bool.False m t s cur_pc i) (function s_M_PC -> 
(match s_M_PC with 
   Matita_freescale_extra.TripleT(s_tmp1,m_op,new_pc) -> 
(match m_op with 
   Matita_freescale_word16.Mk_word16(mH_op,mL_op) -> (let mH_op' = (Matita_freescale_byte8.pred_b8 mH_op) in (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_write Matita_datatypes_bool.True m t s_tmp1 cur_pc i mH_op') (function s_PC -> 
(match s_PC with 
   Matita_datatypes_constructors.Pair(s_tmp2,_) -> 
(match (Matita_freescale_byte8.eq_b8 mH_op' (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))) with 
   Matita_datatypes_bool.True -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp2,new_pc))))
 | Matita_datatypes_bool.False -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp2,(branched_pc m t s_tmp2 new_pc mL_op))))))
)
))))
)
)))))))
;;

let execute_DEC =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_COM_DEC_INC_NEG_aux m t s i cur_pc Matita_freescale_byte8.pred_b8 (function m7 -> (function r7 -> (Matita_freescale_extra.and_bool m7 (Matita_freescale_extra.not_bool r7)))) (function c_op -> (function r_op -> c_op))))))))
;;

let execute_DIV =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_indX_8_high_reg m t s) (function h_op -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_indX_8_low_reg m t s) (function x_op -> 
(match (Matita_freescale_word16.div_b8 (Matita_freescale_word16.Mk_word16(h_op,(Matita_freescale_status.get_acc_8_low_reg m t s))) x_op) with 
   Matita_freescale_extra.TripleT(quoz,rest,overflow) -> (let s_tmp1 = (Matita_freescale_status.set_c_flag m t s overflow) in (let s_tmp2 = 
(match overflow with 
   Matita_datatypes_bool.True -> s_tmp1
 | Matita_datatypes_bool.False -> (Matita_freescale_status.set_acc_8_low_reg m t s_tmp1 quoz))
 in (let s_tmp3 = (Matita_freescale_status.set_z_flag m t s_tmp2 (Matita_freescale_byte8.eq_b8 (Matita_freescale_status.get_acc_8_low_reg m t s_tmp2) (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))) in (Matita_freescale_extra.opt_map 
(match overflow with 
   Matita_datatypes_bool.True -> (Matita_datatypes_constructors.Some(s_tmp3))
 | Matita_datatypes_bool.False -> (Matita_freescale_status.set_indX_8_high_reg m t s_tmp3 rest))
 (function s_tmp4 -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp4,cur_pc))))))))))
)))))))))
;;

let execute_EOR =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_AND_BIT_EOR_ORA_aux m t s i cur_pc Matita_datatypes_bool.True Matita_freescale_byte8.xor_b8))))))
;;

let execute_INC =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_COM_DEC_INC_NEG_aux m t s i cur_pc Matita_freescale_byte8.succ_b8 (function m7 -> (function r7 -> (Matita_freescale_extra.and_bool (Matita_freescale_extra.not_bool m7) r7))) (function c_op -> (function r_op -> c_op))))))))
;;

let execute_JMP =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_load Matita_datatypes_bool.False m t s cur_pc i) (function s_M_PC -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair((Matita_freescale_extra.fst3T s_M_PC),(Matita_freescale_extra.snd3T s_M_PC))))))))))))
;;

let execute_JSR =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_load Matita_datatypes_bool.False m t s cur_pc i) (function s_M_PC -> 
(match s_M_PC with 
   Matita_freescale_extra.TripleT(s_tmp1,m_op,new_pc) -> (let aux = (Matita_freescale_extra.opt_map (aux_push m t s_tmp1 (Matita_freescale_word16.w16l new_pc)) (function s_tmp2 -> (Matita_freescale_extra.opt_map (aux_push m t s_tmp2 (Matita_freescale_word16.w16h new_pc)) (function s_tmp3 -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp3,m_op)))))))) in 
(match m with 
   Matita_freescale_opcode.HC05 -> aux
 | Matita_freescale_opcode.HC08 -> aux
 | Matita_freescale_opcode.HCS08 -> aux
 | Matita_freescale_opcode.RS08 -> (Matita_freescale_extra.opt_map (Matita_freescale_status.set_spc_reg m t s_tmp1 new_pc) (function s_tmp2 -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp2,m_op)))))))
))
)))))))
;;

let execute_LDA =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_load Matita_datatypes_bool.True m t s cur_pc i) (function s_M_PC -> 
(match s_M_PC with 
   Matita_freescale_extra.TripleT(s_tmp1,m_op,new_pc) -> (let s_tmp2 = (Matita_freescale_status.set_acc_8_low_reg m t s_tmp1 m_op) in (let s_tmp3 = (Matita_freescale_status.set_z_flag m t s_tmp2 (Matita_freescale_byte8.eq_b8 m_op (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))) in (let s_tmp4 = (Matita_freescale_status.setweak_n_flag m t s_tmp3 (Matita_freescale_byte8.mSB_b8 m_op)) in (let s_tmp5 = (Matita_freescale_status.setweak_v_flag m t s_tmp4 Matita_datatypes_bool.False) in (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp5,new_pc)))))))))
)))))))
;;

let execute_LDHX =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_load Matita_datatypes_bool.False m t s cur_pc i) (function s_M_PC -> 
(match s_M_PC with 
   Matita_freescale_extra.TripleT(s_tmp1,m_op,new_pc) -> (Matita_freescale_extra.opt_map (Matita_freescale_status.set_indX_16_reg m t s_tmp1 m_op) (function s_tmp2 -> (let s_tmp3 = (Matita_freescale_status.set_z_flag m t s_tmp2 (Matita_freescale_word16.eq_w16 m_op (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))))) in (let s_tmp4 = (Matita_freescale_status.setweak_n_flag m t s_tmp3 (Matita_freescale_word16.mSB_w16 m_op)) in (let s_tmp5 = (Matita_freescale_status.setweak_v_flag m t s_tmp4 Matita_datatypes_bool.False) in (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp5,new_pc))))))))))
)))))))
;;

let execute_LDX =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_load Matita_datatypes_bool.True m t s cur_pc i) (function s_M_PC -> 
(match s_M_PC with 
   Matita_freescale_extra.TripleT(s_tmp1,m_op,new_pc) -> (Matita_freescale_extra.opt_map (Matita_freescale_status.set_indX_8_low_reg m t s_tmp1 m_op) (function s_tmp2 -> (let s_tmp3 = (Matita_freescale_status.set_z_flag m t s_tmp2 (Matita_freescale_byte8.eq_b8 m_op (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))) in (let s_tmp4 = (Matita_freescale_status.setweak_n_flag m t s_tmp3 (Matita_freescale_byte8.mSB_b8 m_op)) in (let s_tmp5 = (Matita_freescale_status.setweak_v_flag m t s_tmp4 Matita_datatypes_bool.False) in (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp5,new_pc))))))))))
)))))))
;;

let execute_LSR =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_ASL_ASR_LSR_ROL_ROR_aux m t s i cur_pc (function m_op -> (function c_op -> (Matita_freescale_byte8.rcr_b8 m_op Matita_datatypes_bool.False)))))))))
;;

let execute_MOV =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_load Matita_datatypes_bool.True m t s cur_pc i) (function s_R_PC -> 
(match s_R_PC with 
   Matita_freescale_extra.TripleT(s_tmp1,r_op,tmp_pc) -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_write Matita_datatypes_bool.True m t s_tmp1 tmp_pc i r_op) (function s_PC -> 
(match s_PC with 
   Matita_datatypes_constructors.Pair(s_tmp2,new_pc) -> (let s_tmp3 = (Matita_freescale_status.set_z_flag m t s_tmp2 (Matita_freescale_byte8.eq_b8 r_op (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))) in (let s_tmp4 = (Matita_freescale_status.setweak_n_flag m t s_tmp3 (Matita_freescale_byte8.mSB_b8 r_op)) in (let s_tmp5 = (Matita_freescale_status.setweak_v_flag m t s_tmp4 Matita_datatypes_bool.False) in (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp5,new_pc))))))))
)))
)))))))
;;

let execute_MUL =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_indX_8_low_reg m t s) (function x_op -> (let r_op = (Matita_freescale_word16.mul_b8 x_op (Matita_freescale_status.get_acc_8_low_reg m t s)) in (Matita_freescale_extra.opt_map (Matita_freescale_status.set_indX_8_low_reg m t s (Matita_freescale_word16.w16h r_op)) (function s_tmp -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair((Matita_freescale_status.set_acc_8_low_reg m t s_tmp (Matita_freescale_word16.w16l r_op)),cur_pc))))))))))))))
;;

let execute_NEG =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_COM_DEC_INC_NEG_aux m t s i cur_pc Matita_freescale_byte8.compl_b8 (function m7 -> (function r7 -> (Matita_freescale_extra.and_bool m7 r7))) (function c_op -> (function r_op -> (Matita_freescale_extra.not_bool (Matita_freescale_byte8.eq_b8 r_op (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))))))))))))
;;

let execute_NOP =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s,cur_pc)))))))))
;;

let execute_NSA =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> 
(match (Matita_freescale_status.get_acc_8_low_reg m t s) with 
   Matita_freescale_byte8.Mk_byte8(ah,al) -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair((Matita_freescale_status.set_acc_8_low_reg m t s (Matita_freescale_byte8.Mk_byte8(al,ah))),cur_pc)))))
)))))
;;

let execute_ORA =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_AND_BIT_EOR_ORA_aux m t s i cur_pc Matita_datatypes_bool.True Matita_freescale_byte8.or_b8))))))
;;

let execute_PSHA =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (aux_push m t s (Matita_freescale_status.get_acc_8_low_reg m t s)) (function s_tmp1 -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp1,cur_pc)))))))))))
;;

let execute_PSHH =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_indX_8_high_reg m t s) (function h_op -> (Matita_freescale_extra.opt_map (aux_push m t s h_op) (function s_tmp1 -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp1,cur_pc)))))))))))))
;;

let execute_PSHX =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_indX_8_low_reg m t s) (function h_op -> (Matita_freescale_extra.opt_map (aux_push m t s h_op) (function s_tmp1 -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp1,cur_pc)))))))))))))
;;

let execute_PULA =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (aux_pop m t s) (function s_and_A -> 
(match s_and_A with 
   Matita_datatypes_constructors.Pair(s_tmp1,a_op) -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair((Matita_freescale_status.set_acc_8_low_reg m t s_tmp1 a_op),cur_pc)))))
)))))))
;;

let execute_PULH =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (aux_pop m t s) (function s_and_H -> 
(match s_and_H with 
   Matita_datatypes_constructors.Pair(s_tmp1,h_op) -> (Matita_freescale_extra.opt_map (Matita_freescale_status.set_indX_8_high_reg m t s_tmp1 h_op) (function s_tmp2 -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp2,cur_pc)))))))
)))))))
;;

let execute_PULX =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (aux_pop m t s) (function s_and_X -> 
(match s_and_X with 
   Matita_datatypes_constructors.Pair(s_tmp1,x_op) -> (Matita_freescale_extra.opt_map (Matita_freescale_status.set_indX_8_low_reg m t s_tmp1 x_op) (function s_tmp2 -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp2,cur_pc)))))))
)))))))
;;

let execute_ROL =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_ASL_ASR_LSR_ROL_ROR_aux m t s i cur_pc (function m_op -> (function c_op -> (Matita_freescale_byte8.rcl_b8 m_op c_op)))))))))
;;

let execute_ROR =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_ASL_ASR_LSR_ROL_ROR_aux m t s i cur_pc (function m_op -> (function c_op -> (Matita_freescale_byte8.rcr_b8 m_op c_op)))))))))
;;

let execute_RSP =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_sp_reg m t s) (function sP_op -> 
(match sP_op with 
   Matita_freescale_word16.Mk_word16(sph,spl) -> (Matita_freescale_extra.opt_map (Matita_freescale_status.set_sp_reg m t s (Matita_freescale_word16.Mk_word16(sph,(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.XF))))) (function s_tmp -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp,cur_pc)))))))
)))))))
;;

let execute_RTI =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (aux_pop m t s) (function s_and_CCR -> 
(match s_and_CCR with 
   Matita_datatypes_constructors.Pair(s_tmp1,cCR_op) -> (let s_tmp2 = (aux_set_CCR m t s_tmp1 cCR_op) in (Matita_freescale_extra.opt_map (aux_pop m t s_tmp2) (function s_and_A -> 
(match s_and_A with 
   Matita_datatypes_constructors.Pair(s_tmp3,a_op) -> (let s_tmp4 = (Matita_freescale_status.set_acc_8_low_reg m t s_tmp3 a_op) in (Matita_freescale_extra.opt_map (aux_pop m t s_tmp4) (function s_and_X -> 
(match s_and_X with 
   Matita_datatypes_constructors.Pair(s_tmp5,x_op) -> (Matita_freescale_extra.opt_map (Matita_freescale_status.set_indX_8_low_reg m t s_tmp5 x_op) (function s_tmp6 -> (Matita_freescale_extra.opt_map (aux_pop m t s_tmp6) (function s_and_PCH -> 
(match s_and_PCH with 
   Matita_datatypes_constructors.Pair(s_tmp7,pCH_op) -> (Matita_freescale_extra.opt_map (aux_pop m t s_tmp7) (function s_and_PCL -> 
(match s_and_PCL with 
   Matita_datatypes_constructors.Pair(s_tmp8,pCL_op) -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp8,(Matita_freescale_word16.Mk_word16(pCH_op,pCL_op)))))))
)))
)))))
))))
))))
)))))))
;;

let execute_RTS =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (let aux = (Matita_freescale_extra.opt_map (aux_pop m t s) (function s_and_PCH -> 
(match s_and_PCH with 
   Matita_datatypes_constructors.Pair(s_tmp1,pCH_op) -> (Matita_freescale_extra.opt_map (aux_pop m t s_tmp1) (function s_and_PCL -> 
(match s_and_PCL with 
   Matita_datatypes_constructors.Pair(s_tmp2,pCL_op) -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp2,(Matita_freescale_word16.Mk_word16(pCH_op,pCL_op)))))))
)))
)) in 
(match m with 
   Matita_freescale_opcode.HC05 -> aux
 | Matita_freescale_opcode.HC08 -> aux
 | Matita_freescale_opcode.HCS08 -> aux
 | Matita_freescale_opcode.RS08 -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_spc_reg m t s) (function sPC_op -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s,sPC_op)))))))
))))))
;;

let execute_SBC =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_SBC_SUB_aux m t s i cur_pc Matita_datatypes_bool.True (function a_op -> (function m_op -> (function c_op -> 
(match (Matita_freescale_byte8.plus_b8 a_op (Matita_freescale_byte8.compl_b8 m_op) Matita_datatypes_bool.False) with 
   Matita_datatypes_constructors.Pair(resb,resc) -> 
(match c_op with 
   Matita_datatypes_bool.True -> (Matita_freescale_byte8.plus_b8 resb (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.XF)) Matita_datatypes_bool.False)
 | Matita_datatypes_bool.False -> (Matita_datatypes_constructors.Pair(resb,resc)))
)
)))))))))
;;

let execute_SEC =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair((Matita_freescale_status.set_c_flag m t s Matita_datatypes_bool.True),cur_pc)))))))))
;;

let execute_SEI =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.set_i_flag m t s Matita_datatypes_bool.True) (function s_tmp -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp,cur_pc)))))))))))
;;

let execute_SHA =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_spc_reg m t s) (function sPC_op -> (Matita_freescale_extra.opt_map (Matita_freescale_status.set_spc_reg m t s (Matita_freescale_word16.Mk_word16((Matita_freescale_status.get_acc_8_low_reg m t s),(Matita_freescale_word16.w16l sPC_op)))) (function s_tmp1 -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair((Matita_freescale_status.set_acc_8_low_reg m t s_tmp1 (Matita_freescale_word16.w16h sPC_op)),cur_pc)))))))))))))
;;

let execute_SLA =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_spc_reg m t s) (function sPC_op -> (Matita_freescale_extra.opt_map (Matita_freescale_status.set_spc_reg m t s (Matita_freescale_word16.Mk_word16((Matita_freescale_word16.w16h sPC_op),(Matita_freescale_status.get_acc_8_low_reg m t s)))) (function s_tmp1 -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair((Matita_freescale_status.set_acc_8_low_reg m t s_tmp1 (Matita_freescale_word16.w16l sPC_op)),cur_pc)))))))))))))
;;

let execute_STA =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (let a_op = (Matita_freescale_status.get_acc_8_low_reg m t s) in (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_write Matita_datatypes_bool.True m t s cur_pc i a_op) (function s_op_and_PC -> 
(match s_op_and_PC with 
   Matita_datatypes_constructors.Pair(s_tmp1,new_pc) -> (let s_tmp2 = (Matita_freescale_status.set_z_flag m t s_tmp1 (Matita_freescale_byte8.eq_b8 a_op (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))) in (let s_tmp3 = (Matita_freescale_status.setweak_n_flag m t s_tmp2 (Matita_freescale_byte8.mSB_b8 a_op)) in (let s_tmp4 = (Matita_freescale_status.setweak_v_flag m t s_tmp3 Matita_datatypes_bool.False) in (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp4,new_pc))))))))
))))))))
;;

let execute_STHX =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_indX_16_reg m t s) (function x_op -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_write Matita_datatypes_bool.False m t s cur_pc i x_op) (function s_op_and_PC -> 
(match s_op_and_PC with 
   Matita_datatypes_constructors.Pair(s_tmp1,new_pc) -> (let s_tmp2 = (Matita_freescale_status.set_z_flag m t s_tmp1 (Matita_freescale_word16.eq_w16 x_op (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))))) in (let s_tmp3 = (Matita_freescale_status.setweak_n_flag m t s_tmp2 (Matita_freescale_word16.mSB_w16 x_op)) in (let s_tmp4 = (Matita_freescale_status.setweak_v_flag m t s_tmp3 Matita_datatypes_bool.False) in (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp4,new_pc))))))))
)))))))))
;;

let execute_STOP =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair((Matita_freescale_status.setweak_i_flag m t s Matita_datatypes_bool.False),cur_pc)))))))))
;;

let execute_STX =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_indX_8_low_reg m t s) (function x_op -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_write Matita_datatypes_bool.True m t s cur_pc i x_op) (function s_op_and_PC -> 
(match s_op_and_PC with 
   Matita_datatypes_constructors.Pair(s_tmp1,new_pc) -> (let s_tmp2 = (Matita_freescale_status.set_z_flag m t s_tmp1 (Matita_freescale_byte8.eq_b8 x_op (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))) in (let s_tmp3 = (Matita_freescale_status.setweak_n_flag m t s_tmp2 (Matita_freescale_byte8.mSB_b8 x_op)) in (let s_tmp4 = (Matita_freescale_status.setweak_v_flag m t s_tmp3 Matita_datatypes_bool.False) in (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp4,new_pc))))))))
)))))))))
;;

let execute_SUB =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (execute_SBC_SUB_aux m t s i cur_pc Matita_datatypes_bool.True (function a_op -> (function m_op -> (function c_op -> (Matita_freescale_byte8.plus_b8 a_op (Matita_freescale_byte8.compl_b8 m_op) Matita_datatypes_bool.False))))))))))
;;

let execute_SWI =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (let vector = (Matita_freescale_status.get_pc_reg m t (Matita_freescale_status.set_pc_reg m t s (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.XF)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.XC)))))) in (Matita_freescale_extra.opt_map (aux_push m t s (Matita_freescale_word16.w16l cur_pc)) (function s_tmp1 -> (Matita_freescale_extra.opt_map (aux_push m t s_tmp1 (Matita_freescale_word16.w16h cur_pc)) (function s_tmp2 -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_indX_8_low_reg m t s_tmp2) (function x_op -> (Matita_freescale_extra.opt_map (aux_push m t s_tmp2 x_op) (function s_tmp3 -> (Matita_freescale_extra.opt_map (aux_push m t s_tmp3 (Matita_freescale_status.get_acc_8_low_reg m t s_tmp3)) (function s_tmp4 -> (Matita_freescale_extra.opt_map (aux_push m t s_tmp4 (aux_get_CCR m t s_tmp4)) (function s_tmp5 -> (Matita_freescale_extra.opt_map (Matita_freescale_status.set_i_flag m t s_tmp5 Matita_datatypes_bool.True) (function s_tmp6 -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.memory_filter_read m t s_tmp6 vector) (function addrh -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.memory_filter_read m t s_tmp6 (Matita_freescale_word16.succ_w16 vector)) (function addrl -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp6,(Matita_freescale_word16.Mk_word16(addrh,addrl))))))))))))))))))))))))))))))
;;

let execute_TAP =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair((aux_set_CCR m t s (Matita_freescale_status.get_acc_8_low_reg m t s)),cur_pc)))))))))
;;

let execute_TAX =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.set_indX_8_low_reg m t s (Matita_freescale_status.get_acc_8_low_reg m t s)) (function s_tmp -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp,cur_pc)))))))))))
;;

let execute_TPA =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair((Matita_freescale_status.set_acc_8_low_reg m t s (aux_get_CCR m t s)),cur_pc)))))))))
;;

let execute_TST =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_load_write.multi_mode_load Matita_datatypes_bool.True m t s cur_pc i) (function s_M_PC -> 
(match s_M_PC with 
   Matita_freescale_extra.TripleT(s_tmp1,m_op,new_pc) -> (let s_tmp2 = (Matita_freescale_status.set_z_flag m t s_tmp1 (Matita_freescale_byte8.eq_b8 m_op (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))) in (let s_tmp3 = (Matita_freescale_status.setweak_n_flag m t s_tmp2 (Matita_freescale_byte8.mSB_b8 m_op)) in (let s_tmp4 = (Matita_freescale_status.setweak_v_flag m t s_tmp3 Matita_datatypes_bool.False) in (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp4,new_pc))))))))
)))))))
;;

let execute_TSX =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_sp_reg m t s) (function sP_op -> (Matita_freescale_extra.opt_map (Matita_freescale_status.set_indX_16_reg m t s (Matita_freescale_word16.succ_w16 sP_op)) (function s_tmp -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp,cur_pc)))))))))))))
;;

let execute_TXA =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_indX_8_low_reg m t s) (function x_op -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair((Matita_freescale_status.set_acc_8_low_reg m t s x_op),cur_pc)))))))))))
;;

let execute_TXS =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_indX_16_reg m t s) (function x_op -> (Matita_freescale_extra.opt_map (Matita_freescale_status.set_sp_reg m t s (Matita_freescale_word16.pred_w16 x_op)) (function s_tmp -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_tmp,cur_pc)))))))))))))
;;

let execute_WAIT =
(function m -> (function t -> (function s -> (function i -> (function cur_pc -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair((Matita_freescale_status.setweak_i_flag m t s Matita_datatypes_bool.False),cur_pc)))))))))
;;

type susp_type =
BGND_MODE
 | STOP_MODE
 | WAIT_MODE
;;

let susp_type_rec =
(function p -> (function p1 -> (function p2 -> (function s -> 
(match s with 
   BGND_MODE -> p
 | STOP_MODE -> p1
 | WAIT_MODE -> p2)
))))
;;

let susp_type_rect =
(function p -> (function p1 -> (function p2 -> (function s -> 
(match s with 
   BGND_MODE -> p
 | STOP_MODE -> p1
 | WAIT_MODE -> p2)
))))
;;

type ('a) tick_result =
TickERR of 'a * Matita_freescale_load_write.error_type
 | TickSUSP of 'a * susp_type
 | TickOK of 'a
;;

let tick_result_rec =
(function f -> (function f1 -> (function f2 -> (function t -> 
(match t with 
   TickERR(t1,e) -> (f t1 e)
 | TickSUSP(t1,s) -> (f1 t1 s)
 | TickOK(t1) -> (f2 t1))
))))
;;

let tick_result_rect =
(function f -> (function f1 -> (function f2 -> (function t -> 
(match t with 
   TickERR(t1,e) -> (f t1 e)
 | TickSUSP(t1,s) -> (f1 t1 s)
 | TickOK(t1) -> (f2 t1))
))))
;;

let tick_execute =
(function m -> (function t -> (function s -> (function pseudo -> (function mode -> (function cur_pc -> (let abs_pseudo = 
(match pseudo with 
   Matita_freescale_opcode.AnyOP(pseudo') -> pseudo')
 in (let a_status_and_fetch = 
(match abs_pseudo with 
   Matita_freescale_opcode.ADC -> (execute_ADC m t s mode cur_pc)
 | Matita_freescale_opcode.ADD -> (execute_ADD m t s mode cur_pc)
 | Matita_freescale_opcode.AIS -> (execute_AIS m t s mode cur_pc)
 | Matita_freescale_opcode.AIX -> (execute_AIX m t s mode cur_pc)
 | Matita_freescale_opcode.AND -> (execute_AND m t s mode cur_pc)
 | Matita_freescale_opcode.ASL -> (execute_ASL m t s mode cur_pc)
 | Matita_freescale_opcode.ASR -> (execute_ASR m t s mode cur_pc)
 | Matita_freescale_opcode.BCC -> (execute_BCC m t s mode cur_pc)
 | Matita_freescale_opcode.BCLRn -> (execute_BCLRn m t s mode cur_pc)
 | Matita_freescale_opcode.BCS -> (execute_BCS m t s mode cur_pc)
 | Matita_freescale_opcode.BEQ -> (execute_BEQ m t s mode cur_pc)
 | Matita_freescale_opcode.BGE -> (execute_BGE m t s mode cur_pc)
 | Matita_freescale_opcode.BGND -> (execute_BGND m t s mode cur_pc)
 | Matita_freescale_opcode.BGT -> (execute_BGT m t s mode cur_pc)
 | Matita_freescale_opcode.BHCC -> (execute_BHCC m t s mode cur_pc)
 | Matita_freescale_opcode.BHCS -> (execute_BHCS m t s mode cur_pc)
 | Matita_freescale_opcode.BHI -> (execute_BHI m t s mode cur_pc)
 | Matita_freescale_opcode.BIH -> (execute_BIH m t s mode cur_pc)
 | Matita_freescale_opcode.BIL -> (execute_BIL m t s mode cur_pc)
 | Matita_freescale_opcode.BIT -> (execute_BIT m t s mode cur_pc)
 | Matita_freescale_opcode.BLE -> (execute_BLE m t s mode cur_pc)
 | Matita_freescale_opcode.BLS -> (execute_BLS m t s mode cur_pc)
 | Matita_freescale_opcode.BLT -> (execute_BLT m t s mode cur_pc)
 | Matita_freescale_opcode.BMC -> (execute_BMC m t s mode cur_pc)
 | Matita_freescale_opcode.BMI -> (execute_BMI m t s mode cur_pc)
 | Matita_freescale_opcode.BMS -> (execute_BMS m t s mode cur_pc)
 | Matita_freescale_opcode.BNE -> (execute_BNE m t s mode cur_pc)
 | Matita_freescale_opcode.BPL -> (execute_BPL m t s mode cur_pc)
 | Matita_freescale_opcode.BRA -> (execute_BRA m t s mode cur_pc)
 | Matita_freescale_opcode.BRCLRn -> (execute_BRCLRn m t s mode cur_pc)
 | Matita_freescale_opcode.BRN -> (execute_BRN m t s mode cur_pc)
 | Matita_freescale_opcode.BRSETn -> (execute_BRSETn m t s mode cur_pc)
 | Matita_freescale_opcode.BSETn -> (execute_BSETn m t s mode cur_pc)
 | Matita_freescale_opcode.BSR -> (execute_BSR m t s mode cur_pc)
 | Matita_freescale_opcode.CBEQA -> (execute_CBEQA m t s mode cur_pc)
 | Matita_freescale_opcode.CBEQX -> (execute_CBEQX m t s mode cur_pc)
 | Matita_freescale_opcode.CLC -> (execute_CLC m t s mode cur_pc)
 | Matita_freescale_opcode.CLI -> (execute_CLI m t s mode cur_pc)
 | Matita_freescale_opcode.CLR -> (execute_CLR m t s mode cur_pc)
 | Matita_freescale_opcode.CMP -> (execute_CMP m t s mode cur_pc)
 | Matita_freescale_opcode.COM -> (execute_COM m t s mode cur_pc)
 | Matita_freescale_opcode.CPHX -> (execute_CPHX m t s mode cur_pc)
 | Matita_freescale_opcode.CPX -> (execute_CPX m t s mode cur_pc)
 | Matita_freescale_opcode.DAA -> (execute_DAA m t s mode cur_pc)
 | Matita_freescale_opcode.DBNZ -> (execute_DBNZ m t s mode cur_pc)
 | Matita_freescale_opcode.DEC -> (execute_DEC m t s mode cur_pc)
 | Matita_freescale_opcode.DIV -> (execute_DIV m t s mode cur_pc)
 | Matita_freescale_opcode.EOR -> (execute_EOR m t s mode cur_pc)
 | Matita_freescale_opcode.INC -> (execute_INC m t s mode cur_pc)
 | Matita_freescale_opcode.JMP -> (execute_JMP m t s mode cur_pc)
 | Matita_freescale_opcode.JSR -> (execute_JSR m t s mode cur_pc)
 | Matita_freescale_opcode.LDA -> (execute_LDA m t s mode cur_pc)
 | Matita_freescale_opcode.LDHX -> (execute_LDHX m t s mode cur_pc)
 | Matita_freescale_opcode.LDX -> (execute_LDX m t s mode cur_pc)
 | Matita_freescale_opcode.LSR -> (execute_LSR m t s mode cur_pc)
 | Matita_freescale_opcode.MOV -> (execute_MOV m t s mode cur_pc)
 | Matita_freescale_opcode.MUL -> (execute_MUL m t s mode cur_pc)
 | Matita_freescale_opcode.NEG -> (execute_NEG m t s mode cur_pc)
 | Matita_freescale_opcode.NOP -> (execute_NOP m t s mode cur_pc)
 | Matita_freescale_opcode.NSA -> (execute_NSA m t s mode cur_pc)
 | Matita_freescale_opcode.ORA -> (execute_ORA m t s mode cur_pc)
 | Matita_freescale_opcode.PSHA -> (execute_PSHA m t s mode cur_pc)
 | Matita_freescale_opcode.PSHH -> (execute_PSHH m t s mode cur_pc)
 | Matita_freescale_opcode.PSHX -> (execute_PSHX m t s mode cur_pc)
 | Matita_freescale_opcode.PULA -> (execute_PULA m t s mode cur_pc)
 | Matita_freescale_opcode.PULH -> (execute_PULH m t s mode cur_pc)
 | Matita_freescale_opcode.PULX -> (execute_PULX m t s mode cur_pc)
 | Matita_freescale_opcode.ROL -> (execute_ROL m t s mode cur_pc)
 | Matita_freescale_opcode.ROR -> (execute_ROR m t s mode cur_pc)
 | Matita_freescale_opcode.RSP -> (execute_RSP m t s mode cur_pc)
 | Matita_freescale_opcode.RTI -> (execute_RTI m t s mode cur_pc)
 | Matita_freescale_opcode.RTS -> (execute_RTS m t s mode cur_pc)
 | Matita_freescale_opcode.SBC -> (execute_SBC m t s mode cur_pc)
 | Matita_freescale_opcode.SEC -> (execute_SEC m t s mode cur_pc)
 | Matita_freescale_opcode.SEI -> (execute_SEI m t s mode cur_pc)
 | Matita_freescale_opcode.SHA -> (execute_SHA m t s mode cur_pc)
 | Matita_freescale_opcode.SLA -> (execute_SLA m t s mode cur_pc)
 | Matita_freescale_opcode.STA -> (execute_STA m t s mode cur_pc)
 | Matita_freescale_opcode.STHX -> (execute_STHX m t s mode cur_pc)
 | Matita_freescale_opcode.STOP -> (execute_STOP m t s mode cur_pc)
 | Matita_freescale_opcode.STX -> (execute_STX m t s mode cur_pc)
 | Matita_freescale_opcode.SUB -> (execute_SUB m t s mode cur_pc)
 | Matita_freescale_opcode.SWI -> (execute_SWI m t s mode cur_pc)
 | Matita_freescale_opcode.TAP -> (execute_TAP m t s mode cur_pc)
 | Matita_freescale_opcode.TAX -> (execute_TAX m t s mode cur_pc)
 | Matita_freescale_opcode.TPA -> (execute_TPA m t s mode cur_pc)
 | Matita_freescale_opcode.TST -> (execute_TST m t s mode cur_pc)
 | Matita_freescale_opcode.TSX -> (execute_TSX m t s mode cur_pc)
 | Matita_freescale_opcode.TXA -> (execute_TXA m t s mode cur_pc)
 | Matita_freescale_opcode.TXS -> (execute_TXS m t s mode cur_pc)
 | Matita_freescale_opcode.WAIT -> (execute_WAIT m t s mode cur_pc))
 in 
(match a_status_and_fetch with 
   Matita_datatypes_constructors.None -> (TickERR((Matita_freescale_status.set_clk_desc m t s (Matita_datatypes_constructors.None)),Matita_freescale_load_write.ILL_EX_AD))
 | Matita_datatypes_constructors.Some(status_and_newpc) -> 
(match status_and_newpc with 
   Matita_datatypes_constructors.Pair(s_tmp1,new_pc) -> (let s_tmp2 = (Matita_freescale_status.set_pc_reg m t s_tmp1 new_pc) in (let s_tmp3 = (Matita_freescale_status.set_clk_desc m t s_tmp2 (Matita_datatypes_constructors.None)) in (let abs_magic = (Matita_freescale_opcode.magic_of_opcode abs_pseudo) in 
(match (Matita_freescale_byte8.eq_b8 abs_magic (Matita_freescale_opcode.magic_of_opcode Matita_freescale_opcode.BGND)) with 
   Matita_datatypes_bool.True -> (TickSUSP(s_tmp3,BGND_MODE))
 | Matita_datatypes_bool.False -> 
(match (Matita_freescale_byte8.eq_b8 abs_magic (Matita_freescale_opcode.magic_of_opcode Matita_freescale_opcode.STOP)) with 
   Matita_datatypes_bool.True -> (TickSUSP(s_tmp3,STOP_MODE))
 | Matita_datatypes_bool.False -> 
(match (Matita_freescale_byte8.eq_b8 abs_magic (Matita_freescale_opcode.magic_of_opcode Matita_freescale_opcode.WAIT)) with 
   Matita_datatypes_bool.True -> (TickSUSP(s_tmp3,WAIT_MODE))
 | Matita_datatypes_bool.False -> (TickOK(s_tmp3)))
)
)
))))
)
))))))))
;;

let tick =
(function m -> (function t -> (function s -> (let opt_info = (Matita_freescale_status.get_clk_desc m t s) in 
(match opt_info with 
   Matita_datatypes_constructors.None -> 
(match (Matita_freescale_load_write.fetch m t s) with 
   Matita_freescale_load_write.FetchERR(err) -> (TickERR(s,err))
 | Matita_freescale_load_write.FetchOK(fetch_info,cur_pc) -> 
(match fetch_info with 
   Matita_freescale_extra.QuadrupleT(pseudo,mode,_,tot_clk) -> 
(match (Matita_freescale_byte8.eq_b8 (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1)) tot_clk) with 
   Matita_datatypes_bool.True -> (tick_execute m t s pseudo mode cur_pc)
 | Matita_datatypes_bool.False -> (TickOK((Matita_freescale_status.set_clk_desc m t s (Matita_datatypes_constructors.Some((Matita_freescale_extra.QuintupleT((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1)),pseudo,mode,tot_clk,cur_pc))))))))
)
)

 | Matita_datatypes_constructors.Some(info) -> 
(match info with 
   Matita_freescale_extra.QuintupleT(cur_clk,pseudo,mode,tot_clk,cur_pc) -> 
(match (Matita_freescale_byte8.eq_b8 (Matita_freescale_byte8.succ_b8 cur_clk) tot_clk) with 
   Matita_datatypes_bool.True -> (tick_execute m t s pseudo mode cur_pc)
 | Matita_datatypes_bool.False -> (TickOK((Matita_freescale_status.set_clk_desc m t s (Matita_datatypes_constructors.Some((Matita_freescale_extra.QuintupleT((Matita_freescale_byte8.succ_b8 cur_clk),pseudo,mode,tot_clk,cur_pc))))))))
)
)
))))
;;

let execute =
let rec execute = 
(function m -> (function t -> (function s -> (function n -> 
(match s with 
   TickERR(s',error) -> print_string("e") ; (TickERR(s',error))
 | TickSUSP(s',susp) -> print_string("s") ; (TickSUSP(s',susp))
 | TickOK(s') -> 
(match n with 
   Matita_nat_nat.O -> (TickOK(s'))
 | Matita_nat_nat.S(n') -> print_string(".") ; (execute m t (tick m t s') n'))
)
)))) in execute
;;
