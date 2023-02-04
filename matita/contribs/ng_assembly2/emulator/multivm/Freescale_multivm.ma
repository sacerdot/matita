(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

(* ********************************************************************** *)
(*                          Progetto FreeScale                            *)
(*                                                                        *)
(*   Sviluppato da: Ing. Cosimo Oliboni, oliboni@cs.unibo.it              *)
(*   Sviluppo: 2008-2010                                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "emulator/multivm/multivm_base.ma".
include "emulator/read_write/load_write.ma".

(* ************************************************ *)
(* LOGICHE AUSILIARE CHE ACCOMUNANO PIU' OPERAZIONI *)
(* ************************************************ *)

(* A = [true] fAMC(A,M,C), [false] A *)
(* cioe' in caso di false l'operazione viene eseguita ma modifica solo i flag *)
(* fAMC e' la logica da applicare: somma con/senza carry *)
ndefinition execute_ADC_ADD_aux ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.λsetflag:bool.
λfAMC:bool → byte8 → byte8 → ProdT bool byte8.
 opt_map … (multi_mode_loadb … s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ triple s_tmp1 M_op new_pc ⇒
    let A_op ≝ get_acc_8_low_reg … s_tmp1 in
    match fAMC (get_c_flag … s_tmp1) A_op M_op with
     [ pair carry R_op ⇒
      let A7 ≝ getMSBc ? A_op in
      let M7 ≝ getMSBc ? M_op in
      let R7 ≝ getMSBc ? R_op in
      let A3 ≝ getMSBc ? (cnL ? A_op) in
      let M3 ≝ getMSBc ? (cnL ? M_op) in
      let R3 ≝ getMSBc ? (cnL ? R_op) in
      (* A = [true] fAMC(A,M,C), [false] A *)
      let s_tmp2 ≝ match setflag with [ true ⇒ set_acc_8_low_reg … s_tmp1 R_op | false ⇒ s_tmp1 ] in
      (* Z = nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
      let s_tmp3 ≝ set_zflb … s_tmp2 R_op in
      (* C = A7&M7 | M7&nR7 | nR7&A7 *)
      let s_tmp4 ≝ set_c_flag … s_tmp3 ((A7⊗M7) ⊕ (M7⊗(⊖R7)) ⊕ ((⊖R7)⊗A7)) in
      (* N = R7 *)
      let s_tmp5 ≝ set_nflb … s_tmp4 R_op in
      (* H = A3&M3 | M3&nR3 | nR3&A3 *)
      let s_tmp6 ≝ setweak_h_flag … s_tmp5 ((A3⊗M3) ⊕ (M3⊗(⊖R3)) ⊕ ((⊖R3)⊗A3)) in
      (* V = A7&M7&nR7 | nA7&nM7&R7 *)
      let s_tmp7 ≝ setweak_v_flag … s_tmp6 ((A7⊗M7⊗(⊖R7)) ⊕ ((⊖A7)⊗(⊖M7)⊗R7)) in
      (* newpc = nextpc *)
      Some ? (pair … s_tmp7 new_pc) ]]).

(* A = [true] fAM(A,M), [false] A *)
(* cioe' in caso di false l'operazione viene eseguita ma modifica solo i flag *)
(* fAM e' la logica da applicare: and/xor/or *)
ndefinition execute_AND_BIT_EOR_ORA_aux ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.λsetflag:bool.
λfAM:byte8 → byte8 → byte8.
 opt_map … (multi_mode_loadb … s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ triple s_tmp1 M_op new_pc ⇒
    let R_op ≝ fAM (get_acc_8_low_reg … s_tmp1) M_op in
    (* A = [true] fAM(A,M), [false] A *) 
    let s_tmp2 ≝ match setflag with [ true ⇒ set_acc_8_low_reg … s_tmp1 R_op | false ⇒ s_tmp1 ] in
    (* Z = nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
    let s_tmp3 ≝ set_zflb … s_tmp2 R_op in
    (* N = R7 *) 
    let s_tmp4 ≝ set_nflb … s_tmp3 R_op in
    (* V = 0 *) 
    let s_tmp5 ≝ setweak_v_flag … s_tmp4 false in
    (* newpc = nextpc *)
    Some ? (pair … s_tmp5 new_pc) ]).

(* M = fMC(M,C) *)
(* fMC e' la logica da applicare: rc_/ro_/sh_ *)
ndefinition execute_ASL_ASR_LSR_ROL_ROR_aux ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
λfMC:bool → byte8 → ProdT bool byte8.
 opt_map … (multi_mode_loadb … s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ triple s_tmp1 M_op _ ⇒
    match fMC (get_c_flag … s_tmp1) M_op with [ pair carry R_op ⇒
    (* M = fMC(M,C) *)
    opt_map … (multi_mode_writeb … s_tmp1 cur_pc auxMode_ok i R_op)
     (λS_PC.match S_PC with
      [ pair s_tmp2 new_pc ⇒
      (* C = carry *)
      let s_tmp3 ≝ set_c_flag … s_tmp2 carry in
      (* Z = nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
      let s_tmp4 ≝ set_zflb … s_tmp3 R_op in
      (* N = R7 *)
      let s_tmp5 ≝ set_nflb … s_tmp4 R_op in
      (* V = R7 ⊙ carry *)
      let s_tmp6 ≝ setweak_v_flag … s_tmp5 ((getMSBc ? R_op) ⊙ carry) in
      (* newpc = nextpc *)
      Some ? (pair … s_tmp6 new_pc) ])]]).

(* branch con byte+estensione segno *)
ndefinition branched_pc ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λb:byte8.
 get_pc_reg … (set_pc_reg … s (plusc_d_d ? cur_pc (exts_w16  b))).

(* if COND=1 branch *)
(* tutti i branch calcoleranno la condizione e la passeranno qui *)
ndefinition execute_any_BRANCH ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.λfCOND:bool.
 opt_map … (multi_mode_loadb … s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ triple s_tmp1 M_op new_pc ⇒
    (* if true, branch *) 
    match fCOND with
     (* newpc = nextpc + rel *)
     [ true ⇒ Some ? (pair … s_tmp1 (branched_pc … s_tmp1 new_pc M_op))
     (* newpc = nextpc *)
     | false ⇒ Some ? (pair … s_tmp1 new_pc) ]]).

(* Mn = filtered optval *) 
(* il chiamante passa 0x00 per azzerare, 0xFF per impostare il bit di M *)
ndefinition execute_BCLRn_BSETn_aux ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.λoptval:byte8.
 (* Mn = filtered optval *)
 opt_map … (multi_mode_writeb … s cur_pc auxMode_ok i optval)
  (λS_PC.match S_PC with
   (* newpc = nextpc *)
   [ pair s_tmp1 new_pc ⇒ Some ? (pair … s_tmp1 new_pc) ]).

(* if COND(Mn) branch *)
(* il chiamante passa la logica da testare (0x00,¬0x00) e poi si salta *)
ndefinition execute_BRCLRn_BRSETn_aux ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.λfCOND:byte8 → bool.
 opt_map … (multi_mode_loadw … s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ triple s_tmp1 M_op new_pc ⇒ match M_op with
    [ mk_comp_num MH_op ML_op ⇒
     (* if COND(Mn) branch *)
     match fCOND MH_op with
      (* newpc = nextpc + rel *)
      [ true ⇒ Some ? (pair … s_tmp1 (branched_pc … s_tmp1 new_pc ML_op))
      (* newpc = nextpc *)
      | false ⇒ Some ? (pair … s_tmp1 new_pc) ]]]).

(* A = [true] fAMC(A,M,C), [false] A *)
(* cioe' in caso di false l'operazione viene eseguita ma modifica solo i flag *)
(* fAMC e' la logica da applicare: sottrazione con/senza carry *)
ndefinition execute_CMP_SBC_SUB_aux ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.λsetflag:bool.
λfAMC:bool → byte8 → byte8 → ProdT bool byte8.
 opt_map … (multi_mode_loadb … s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ triple s_tmp1 M_op new_pc ⇒
    let A_op ≝ get_acc_8_low_reg … s_tmp1 in
    match fAMC (get_c_flag … s_tmp1) A_op M_op with
     [ pair carry R_op ⇒
      let A7 ≝ getMSBc ? A_op in
      let M7 ≝ getMSBc ? M_op in
      let R7 ≝ getMSBc ? R_op in
      (* A = [true] fAMC(A,M,C), [false] A *)
      let s_tmp2 ≝ match setflag with [ true ⇒ set_acc_8_low_reg … s_tmp1 R_op | false ⇒ s_tmp1 ] in
      (* Z = nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
      let s_tmp3 ≝ set_zflb … s_tmp2 R_op in
      (* C = nA7&M7 | M7&R7 | R7&nA7 *)
      let s_tmp4 ≝ set_c_flag … s_tmp3 (((⊖A7)⊗M7) ⊕ (M7⊗R7) ⊕ (R7⊗(⊖A7))) in
      (* N = R7 *) 
      let s_tmp5 ≝ set_nflb … s_tmp4 R_op in
      (* V = A7&nM7&nR7 | nA7&M7&R7 *)
      let s_tmp6 ≝ setweak_v_flag … s_tmp5 ((A7⊗(⊖M7)⊗(⊖R7)) ⊕ ((⊖A7)⊗M7⊗R7)) in
      (* newpc = nextpc *)
      Some ? (pair … s_tmp6 new_pc) ]]).

(* M = fM(M) *)
(* fM e' la logica da applicare: not/neg/++/-- *)
ndefinition execute_COM_DEC_INC_NEG_aux ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
λfM:byte8 → byte8.λfV:bool → bool → bool.λfC:bool → byte8 → bool.
 opt_map … (multi_mode_loadb … s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ triple s_tmp1 M_op _ ⇒
    let R_op ≝ fM M_op in
    (* M = fM(M) *)
    opt_map … (multi_mode_writeb … s_tmp1 cur_pc auxMode_ok i R_op)
     (λS_PC.match S_PC with
      [ pair s_tmp2 new_pc ⇒
      (* C = fCR (C,R) *)
      let s_tmp3 ≝ set_c_flag … s_tmp2 (fC (get_c_flag … s_tmp2) R_op) in
      (* Z = nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
      let s_tmp4 ≝ set_zflb … s_tmp3 R_op in
      (* N = R7 *)
      let s_tmp5 ≝ set_nflb … s_tmp4 R_op in
      (* V = fV (M7,R7) *)
      let s_tmp6 ≝ setweak_v_flag … s_tmp5 (fV (getMSBc ? M_op) (getMSBc ? R_op)) in
      (* newpc = nextpc *)
      Some ? (pair … s_tmp6 new_pc) ])]).

(* il classico push *)
ndefinition aux_push ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval:byte8.
 opt_map … (get_sp_reg … s)
  (* [SP] = val *)
  (λSP_op.opt_map … (memory_filter_write … s SP_op auxMode_ok val)
   (* SP -- *)
   (λs_tmp1.opt_map … (set_sp_reg … s_tmp1 (predc ? SP_op))
    (λs_tmp2.Some ? s_tmp2))).

(* il classico pop *)
(* NB: l'incremento di SP deve essere filtrato dalla ALU, quindi get(set(SP)) *)
ndefinition aux_pop ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 opt_map … (get_sp_reg … s)
  (* SP ++ *)
  (λSP_op.opt_map … (set_sp_reg … s (succc ? SP_op))
   (λs_tmp1.opt_map … (get_sp_reg … s_tmp1)
    (* val = [SP] *)
    (λSP_op'.opt_map … (memory_filter_read … s_tmp1 SP_op')
     (λval.Some ? (pair … s_tmp1 val))))).

(* CCR corrisponde a V11HINZC e cmq 1 se un flag non esiste *)
(* i flag mantengono posizione costante nelle varie ALU, e se non sono
   implementati corrispondono a 1 *)
ndefinition aux_get_CCR_aux ≝
λopt:option bool.match opt with [ None ⇒ true | Some b ⇒ b ].

ndefinition aux_get_CCR ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 byte8_of_bits (mk_Array8T ?
  (aux_get_CCR_aux (get_v_flag … s))
  true
  true
  (aux_get_CCR_aux (get_h_flag … s))
  (aux_get_CCR_aux (get_i_flag … s))
  (aux_get_CCR_aux (get_n_flag … s))
  (get_z_flag … s)
  (get_c_flag … s)).

(* CCR corrisponde a V11HINZC *)
(* i flag mantengono posizione costante nelle varie ALU, e se non sono
   implementati si puo' usare tranquillamente setweak *)
ndefinition aux_set_CCR ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λCCR:byte8.
 match bits_of_byte8 CCR with
  [ mk_Array8T vf _ _ hf if nf zf cf ⇒
   setweak_v_flag …
    (setweak_h_flag …
     (setweak_i_flag …
      (setweak_n_flag …
       (set_z_flag …
        (set_c_flag … s cf) zf) nf) if) hf) vf ].

(* **************** *)
(* LOGICA DELLA ALU *)
(* **************** *)

(* A = A + M + C *)
ndefinition execute_ADC ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_ADC_ADD_aux … s cur_pc i true (λC_op.plusc_dc_dc ? C_op).

(* A = A + M *)
ndefinition execute_ADD ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_ADC_ADD_aux … s cur_pc i true (λC_op.plusc_dc_dc ? false).

(* SP += extended M *)
ndefinition execute_AIS ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (multi_mode_loadb … s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ triple s_tmp1 M_op new_pc ⇒
   opt_map … (get_sp_reg … s_tmp1)
    (* SP += extended M *)
    (λSP_op.opt_map … (set_sp_reg … s_tmp1 (plusc_d_d ? SP_op (exts_w16 M_op)))
     (λs_tmp2.Some ? (pair … s_tmp2 new_pc))) ]).

(* H:X += extended M *)
ndefinition execute_AIX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (multi_mode_loadb … s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ triple s_tmp1 M_op new_pc ⇒
   opt_map … (get_indX_16_reg … s_tmp1)
    (* H:X += extended M *)
    (λHX_op.opt_map … (set_indX_16_reg … s_tmp1 (plusc_d_d ? HX_op (exts_w16 M_op)))
     (λs_tmp2.Some ? (pair … s_tmp2 new_pc))) ]).

(* A = A & M *)
ndefinition execute_AND ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_AND_BIT_EOR_ORA_aux … s cur_pc i true (andc ?).

(* M = C' <- rcl M <- 0 *)
ndefinition execute_ASL ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_ASL_ASR_LSR_ROL_ROR_aux … s cur_pc i (λC_op.rclc ? false).

(* M = M7 -> rcr M -> C' *)
ndefinition execute_ASR ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_ASL_ASR_LSR_ROL_ROR_aux … s cur_pc i (λC_op.λM_op.rcrc ? (getMSBc ? M_op) M_op).

(* if C=0, branch *) 
ndefinition execute_BCC ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_any_BRANCH … s cur_pc i (⊖(get_c_flag … s)).

(* Mn = 0 *)
ndefinition execute_BCLRn ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_BCLRn_BSETn_aux … s cur_pc i 〈x0,x0〉.

(* if C=1, branch *) 
ndefinition execute_BCS ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_any_BRANCH … s cur_pc i (get_c_flag … s).

(* if Z=1, branch *)
ndefinition execute_BEQ ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_any_BRANCH … s cur_pc i (get_z_flag … s).

(* if N⊙V=0, branch *)
ndefinition execute_BGE ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (get_n_flag … s)
  (λN_op.opt_map … (get_v_flag … s)
   (λV_op.execute_any_BRANCH … s cur_pc i (⊖(N_op ⊙ V_op)))).

(* BGND mode *)
ndefinition execute_BGND ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 Some ? (pair … s cur_pc).

(* if Z|N⊙V=0, branch *)
ndefinition execute_BGT ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (get_n_flag … s)
  (λN_op.opt_map … (get_v_flag … s)
   (λV_op.execute_any_BRANCH … s cur_pc i (⊖((get_z_flag … s) ⊕ (N_op ⊙ V_op))))).

(* if H=0, branch *)
ndefinition execute_BHCC ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (get_h_flag … s)
  (λH_op.execute_any_BRANCH … s cur_pc i (⊖H_op)).

(* if H=1, branch *)
ndefinition execute_BHCS ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (get_h_flag … s)
  (λH_op.execute_any_BRANCH … s cur_pc i H_op).

(* if C|Z=0, branch *)
ndefinition execute_BHI ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_any_BRANCH … s cur_pc i (⊖((get_c_flag … s) ⊕ (get_z_flag … s))).

(* if nIRQ=1, branch NB: irqflag e' un negato del pin *)
ndefinition execute_BIH ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (get_irq_flag … s)
  (λIRQ_op.execute_any_BRANCH … s cur_pc i (⊖IRQ_op)).

(* if nIRQ=0, branch NB: irqflag e' un negato del pin *)
ndefinition execute_BIL ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (get_irq_flag … s)
  (λIRQ_op.execute_any_BRANCH … s cur_pc i IRQ_op).

(* flags = A & M *)
ndefinition execute_BIT ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_AND_BIT_EOR_ORA_aux … s cur_pc i false (andc ?).

(* if Z|N⊙V=1, branch *)
ndefinition execute_BLE ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (get_n_flag … s)
  (λN_op.opt_map … (get_v_flag … s)
   (λV_op.execute_any_BRANCH … s cur_pc i ((get_z_flag … s) ⊕ (N_op ⊙ V_op)))).

(* if C|Z=1, branch *)
ndefinition execute_BLS ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_any_BRANCH … s cur_pc i ((get_c_flag … s) ⊕ (get_z_flag … s)).

(* if N⊙V=1, branch *)
ndefinition execute_BLT ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (get_n_flag … s)
  (λN_op.opt_map … (get_v_flag … s)
   (λV_op.execute_any_BRANCH … s cur_pc i (N_op ⊙ V_op))).

(* if I=0, branch *)
ndefinition execute_BMC ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (get_i_flag … s)
  (λI_op.execute_any_BRANCH … s cur_pc i (⊖I_op)).

(* if N=1, branch *)
ndefinition execute_BMI ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (get_n_flag … s)
  (λN_op.execute_any_BRANCH … s cur_pc i N_op).

(* if I=1, branch *)
ndefinition execute_BMS ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (get_i_flag … s)
  (λI_op.execute_any_BRANCH … s cur_pc i I_op).

(* if Z=0, branch *)
ndefinition execute_BNE ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_any_BRANCH … s cur_pc i (⊖(get_z_flag … s)).

(* if N=0, branch *)
ndefinition execute_BPL ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (get_n_flag … s)
  (λN_op.execute_any_BRANCH … s cur_pc i (⊖N_op)).

(* branch always *)
ndefinition execute_BRA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_any_BRANCH … s cur_pc i true.

(* if Mn=0 branch *)
ndefinition execute_BRCLRn ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_BRCLRn_BRSETn_aux … s cur_pc i
  (λMn_op.eqc ? Mn_op (zeroc ?)).

(* branch never... come se fosse un nop da 2 byte *)
ndefinition execute_BRN ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_any_BRANCH … s cur_pc i false.

(* if Mn=1 branch *)
ndefinition execute_BRSETn ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_BRCLRn_BRSETn_aux … s cur_pc i
  (λMn_op.⊖(eqc ? Mn_op (zeroc ?))).

(* Mn = 1 *)
ndefinition execute_BSETn ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_BCLRn_BSETn_aux … s cur_pc i 〈xF,xF〉.

(* branch to subroutine *)
(* HC05/HC08/HCS08 si appoggiano allo stack, RS08 a SPC *)
ndefinition execute_BSR ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t .λcur_pc:word16.λi:aux_im_type m.
 opt_map … (multi_mode_loadb … s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ triple s_tmp1 M_op new_pc ⇒ let aux ≝
    (* push (new_pc low) *)
    opt_map … (aux_push … s_tmp1 (cnL ? new_pc))
     (* push (new_pc high) *)
     (λs_tmp2.opt_map … (aux_push … s_tmp2 (cnH ? new_pc))
      (* new_pc = new_pc + rel *)
      (λs_tmp3.Some ? (pair … s_tmp3 (branched_pc … s_tmp3 new_pc M_op))))
     in match m with
    [ HC05 ⇒ aux | HC08 ⇒ aux | HCS08 ⇒ aux
    | RS08 ⇒
     (* SPC = new_pc *) 
     opt_map … (set_spc_reg … s_tmp1 new_pc)
      (* new_pc = new_pc + rel *)
      (λs_tmp2.Some ? (pair … s_tmp2 (branched_pc … s_tmp2 new_pc M_op)))
    | _ ⇒ None ?
    ]]).

(* if A=M, branch *)
ndefinition execute_CBEQA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (multi_mode_loadw … s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ triple s_tmp1 M_op new_pc ⇒
    match M_op with
     [ mk_comp_num MH_op ML_op ⇒
      (* if A=M, branch *)
      match eqc ? (get_acc_8_low_reg … s_tmp1) MH_op with
       (* new_pc = new_pc + rel *)
       [ true ⇒ Some ? (pair … s_tmp1 (branched_pc … s_tmp1 new_pc ML_op))
       (* new_pc = new_pc *)
       | false ⇒ Some ? (pair … s_tmp1 new_pc)
       ]]]).

(* if X=M, branch *)
ndefinition execute_CBEQX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (multi_mode_loadw … s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ triple s_tmp1 M_op new_pc ⇒
    match M_op with
     [ mk_comp_num MH_op ML_op ⇒
      opt_map … (get_indX_8_low_reg … s_tmp1)
       (* if X=M, branch *)
       (λX_op.match eqc ? X_op MH_op with
        (* new_pc = new_pc + rel *)
        [ true ⇒ Some ? (pair … s_tmp1 (branched_pc … s_tmp1 new_pc ML_op))
        (* new_pc = new_pc *)
        | false ⇒ Some ? (pair … s_tmp1 new_pc)
        ])]]).

(* C = 0 *)
ndefinition execute_CLC ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 Some ? (pair … (set_c_flag … s false) cur_pc).

(* I = 0 *)
ndefinition execute_CLI ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (set_i_flag … s false)
  (λs_tmp.Some ? (pair … s_tmp cur_pc)).

(* M = 0 *)
ndefinition execute_CLR ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 (* M = 0 *)
 opt_map … (multi_mode_writeb … s cur_pc auxMode_ok i 〈x0,x0〉)
  (λS_PC.match S_PC with
   [ pair s_tmp1 new_pc ⇒
   (* Z = 1 *)
   let s_tmp2 ≝ set_z_flag … s_tmp1 true in
   (* N = 0 *)
   let s_tmp3 ≝ setweak_n_flag … s_tmp2 false in
   (* V = 0 *)
   let s_tmp4 ≝ setweak_v_flag … s_tmp3 false in
   (* newpc = nextpc *)
   Some ? (pair … s_tmp4 new_pc) ]).

(* flags = A - M *)
ndefinition execute_CMP ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_CMP_SBC_SUB_aux … s cur_pc i false (λC_op.λA_op.λM_op.plusc_dc_dc ? false A_op (complc ? M_op)). 

(* M = not M *)
ndefinition execute_COM ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_COM_DEC_INC_NEG_aux … s cur_pc i (notc ?)
 (* fV = 0 *)
 (λM7.λR7.false)
 (* fC = 1 *)
 (λC_op.λR_op.true).

(* flags = H:X - M *)
ndefinition execute_CPHX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (multi_mode_loadw … s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ triple s_tmp1 M_op new_pc ⇒
    opt_map … (get_indX_16_reg … s_tmp1)
     (λX_op. 
      match plusc_dc_dc ? false X_op (complc ? M_op) with
       [ pair carry R_op ⇒
        let X15 ≝ getMSBc ? X_op in
        let M15 ≝ getMSBc ? M_op in
        let R15 ≝ getMSBc ? R_op in
        (* Z = nR15&nR14&nR13&nR12&nR11&nR10&nR9&nR8&nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
        let s_tmp2 ≝ set_zflw … s_tmp1 R_op in
        (* C = nX15&M15 | M15&R15 | R15&nX15 *)
        let s_tmp3 ≝ set_c_flag … s_tmp2 (((⊖X15)⊗M15) ⊕ (M15⊗R15) ⊕ (R15⊗(⊖X15))) in
        (* N = R15 *) 
        let s_tmp4 ≝ set_nflw … s_tmp3 R_op in
        (* V = X15&nM15&nR15 | nX15&M15&R15 *)
        let s_tmp5 ≝ setweak_v_flag … s_tmp4 ((X15⊗(⊖M15)⊗(⊖R15)) ⊕ ((⊖X15)⊗M15⊗R15)) in
        (* newpc = nextpc *)
        Some ? (pair … s_tmp5 new_pc) ] ) ]).

(* flags = X - M *)
ndefinition execute_CPX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (multi_mode_loadb … s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ triple s_tmp1 M_op new_pc ⇒
    opt_map … (get_indX_8_low_reg … s_tmp1)
     (λX_op. 
      match plusc_dc_dc ? false X_op (complc ? M_op) with
       [ pair carry R_op ⇒
        let X7 ≝ getMSBc ? X_op in
        let M7 ≝ getMSBc ? M_op in
        let R7 ≝ getMSBc ? R_op in
        (* Z = nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
        let s_tmp2 ≝ set_zflb … s_tmp1 R_op in
        (* C = nX7&M7 | M7&R7 | R7&nX7 *)
        let s_tmp3 ≝ set_c_flag … s_tmp2 (((⊖X7)⊗M7) ⊕ (M7⊗R7) ⊕ (R7⊗(⊖X7))) in
        (* N = R7 *) 
        let s_tmp4 ≝ set_nflb … s_tmp3 R_op in
        (* V = X7&nM7&nR7 | nX7&M7&R7 *)
        let s_tmp5 ≝ setweak_v_flag … s_tmp4 ((X7⊗(⊖M7)⊗(⊖R7)) ⊕ ((⊖X7)⊗M7⊗R7)) in
        (* newpc = nextpc *)
        Some ? (pair … s_tmp5 new_pc) ] ) ]).

(* decimal adjiust A *)
(* per i dettagli vedere daa_b8 (modulo byte8) *)
ndefinition execute_DAA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (get_h_flag … s)
  (λH.
   let M_op ≝ get_acc_8_low_reg … s in
   match daa_b8 H (get_c_flag … s) M_op with
    [ pair carry R_op ⇒
     (* A = R *)
     let s_tmp1 ≝ set_acc_8_low_reg … s R_op in
     (* Z = nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
     let s_tmp2 ≝ set_zflb … s_tmp1 R_op in
     (* C = carry *)
     let s_tmp3 ≝ set_c_flag … s_tmp2 carry in
     (* N = R7 *) 
     let s_tmp4 ≝ set_nflb … s_tmp3 R_op in
     (* V = M7 ⊙ R7 *)
     let s_tmp5 ≝ setweak_v_flag … s_tmp4 ((getMSBc ? M_op) ⊙ (getMSBc ? R_op)) in
     (* newpc = curpc *)
     Some ? (pair … s_tmp5 cur_pc) ]).

(* if (--M)≠0, branch *)
ndefinition execute_DBNZ ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (multi_mode_loadw … s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ triple s_tmp1 M_op new_pc ⇒
    match M_op with
     [ mk_comp_num MH_op ML_op ⇒
     (* --M *)
     let MH_op' ≝ predc ? MH_op in
     opt_map … (multi_mode_writeb … s_tmp1 cur_pc auxMode_ok i MH_op')
      (λS_PC.match S_PC with
       [ pair s_tmp2 _ ⇒
        (* if (--M)≠0, branch *)
        match eqc ? MH_op' (zeroc ?) with
         (* new_pc = new_pc *)
         [ true ⇒ Some ? (pair … s_tmp2 new_pc)
         (* new_pc = new_pc + rel *)
         | false ⇒ Some ? (pair … s_tmp2 (branched_pc … s_tmp2 new_pc ML_op)) ]])]]).

(* M = M - 1 *)
ndefinition execute_DEC ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_COM_DEC_INC_NEG_aux … s cur_pc i (predc ?)
 (* fV = M7&nR7 *)
 (λM7.λR7.M7⊗(⊖R7))
 (* fC = C *)
 (λC_op.λR_op.C_op).

(* A = H:A/X, H = H:AmodX se non c'e' overflow, altrimenti invariati *)
(* per i dettagli vedere div_b8 (modulo word16) *)
ndefinition execute_DIV ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (get_indX_8_high_reg … s)
  (λH_op.opt_map … (get_indX_8_low_reg … s)
   (λX_op.match div_b8 〈H_op:(get_acc_8_low_reg … s)〉 X_op with
    [ triple quoz rest overflow ⇒
     (* C = overflow *)
     let s_tmp1 ≝ set_c_flag … s overflow in
     (* A = A o H:A/X *)
     let s_tmp2 ≝ match overflow with
      [ true ⇒ s_tmp1
      | false ⇒ set_acc_8_low_reg … s_tmp1 quoz ] in
     (* Z = nA7&nA6&nA5&nA4&nA3&nA2&nA1&nA0 *)
     (* NB: che A sia cambiato o no, lo testa *)
     let s_tmp3 ≝ set_zflb … s_tmp2 (get_acc_8_low_reg … s_tmp2) in
     (* H = H o H:AmodX *)
     opt_map … (match overflow with
                 [ true ⇒ Some ? s_tmp3
                 | false ⇒ set_indX_8_high_reg … s_tmp3 rest])
      (λs_tmp4.Some ? (pair … s_tmp4 cur_pc)) ])).

(* A = A ⊙ M *)
ndefinition execute_EOR ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_AND_BIT_EOR_ORA_aux … s cur_pc i true (xorc ?).

(* M = M + 1 *)
ndefinition execute_INC ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_COM_DEC_INC_NEG_aux … s cur_pc i (succc ?)
 (* fV = nM7&R7 *)
 (λM7.λR7.(⊖M7)⊗R7)
 (* fC = C *)
 (λC_op.λR_op.C_op).

(* jmp, il nuovo indirizzo e' una WORD *)
ndefinition execute_JMP ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (multi_mode_loadw … s cur_pc i)
  (λS_M_PC.
   (* newpc = M_op *)
   Some ? (pair … (fst3T … S_M_PC) (snd3T … S_M_PC))).

(* jump to subroutine *)
(* HC05/HC08/HCS08 si appoggiano allo stack, RS08 a SPC *)
ndefinition execute_JSR ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (multi_mode_loadw … s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ triple s_tmp1 M_op new_pc ⇒ let aux ≝
    (* push (new_pc low) *)
    opt_map … (aux_push … s_tmp1 (cnL ? new_pc))
     (* push (new_pc high) *)
     (λs_tmp2.opt_map … (aux_push … s_tmp2 (cnH ? new_pc))
      (* newpc = M_op *)
      (λs_tmp3.Some ? (pair … s_tmp3 M_op)))
     in match m with
    [ HC05 ⇒ aux | HC08 ⇒ aux | HCS08 ⇒ aux
    | RS08 ⇒
     (* SPC = new_pc *) 
     opt_map … (set_spc_reg … s_tmp1 new_pc)
      (* newpc = M_op *)
      (λs_tmp2.Some ? (pair … s_tmp2 M_op))
    | _ ⇒ None ?
    ]]).

(* A = M *)
ndefinition execute_LDA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (multi_mode_loadb … s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ triple s_tmp1 M_op new_pc ⇒
    (* A = M *) 
    let s_tmp2 ≝ set_acc_8_low_reg … s_tmp1 M_op in
    (* Z = nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
    let s_tmp3 ≝ set_zflb … s_tmp2 M_op in
    (* N = R7 *) 
    let s_tmp4 ≝ set_nflb … s_tmp3 M_op in
    (* V = 0 *) 
    let s_tmp5 ≝ setweak_v_flag … s_tmp4 false in
    (* newpc = nextpc *)
    Some ? (pair … s_tmp5 new_pc) ]).

(* H:X = M *)
ndefinition execute_LDHX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (multi_mode_loadw … s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ triple s_tmp1 M_op new_pc ⇒
    opt_map … (set_indX_16_reg … s_tmp1 M_op)
     (λs_tmp2.
      (* Z = nR15&nR14&nR13nR12&nR11&nR10&nR9&nR8nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
      let s_tmp3 ≝ set_zflw … s_tmp2 M_op in
      (* N = R15 *)
      let s_tmp4 ≝ set_nflw … s_tmp3 M_op in
      (* V = 0 *) 
      let s_tmp5 ≝ setweak_v_flag … s_tmp4 false in
      (* newpc = nextpc *)
      Some ? (pair … s_tmp5 new_pc)) ]).

(* X = M *)
ndefinition execute_LDX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (multi_mode_loadb … s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ triple s_tmp1 M_op new_pc ⇒
    opt_map … (set_indX_8_low_reg … s_tmp1 M_op)
     (λs_tmp2.
      (* Z = nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
      let s_tmp3 ≝ set_zflb … s_tmp2 M_op in
      (* N = R7 *)
      let s_tmp4 ≝ set_nflb … s_tmp3 M_op in
      (* V = 0 *) 
      let s_tmp5 ≝ setweak_v_flag … s_tmp4 false in
      (* newpc = nextpc *)
      Some ? (pair … s_tmp5 new_pc)) ]).

(* M = 0 -> rcr M -> C' *)
ndefinition execute_LSR ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_ASL_ASR_LSR_ROL_ROR_aux … s cur_pc i (λC_op.λM_op.rcrc ? false M_op).

(* M2 = M1 *)
ndefinition execute_MOV ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 (* R_op = M1 *)
 opt_map … (multi_mode_loadb … s cur_pc i)
  (λS_R_PC.match S_R_PC with
   [ triple s_tmp1 R_op tmp_pc ⇒
    (* M2 = R_op *)
    opt_map … (multi_mode_writeb … s_tmp1 tmp_pc auxMode_ok i R_op)
     (λS_PC.match S_PC with
      [ pair s_tmp2 new_pc ⇒
       (* Z = nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
       let s_tmp3 ≝ set_zflb … s_tmp2 R_op in
       (* N = R7 *)
       let s_tmp4 ≝ set_nflb … s_tmp3 R_op in
       (* V = 0 *) 
       let s_tmp5 ≝ setweak_v_flag … s_tmp4 false in
       (* newpc = nextpc *)
       Some ? (pair … s_tmp5 new_pc)])]).

(* X:A = X * A *)
ndefinition execute_MUL ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (get_indX_8_low_reg … s)
  (λX_op.let R_op ≝ mulu_b8 X_op (get_acc_8_low_reg … s) in
   opt_map … (set_indX_8_low_reg … s (cnH ? R_op))
    (λs_tmp.Some ? (pair … (set_acc_8_low_reg … s_tmp (cnL ? R_op)) cur_pc))).

(* M = compl M *)
ndefinition execute_NEG ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_COM_DEC_INC_NEG_aux … s cur_pc i (complc ?)
 (* fV = M7&R7 *)
 (λM7.λR7.M7⊗R7)
 (* fC = R7|R6|R5|R4|R3|R2|R1|R0 *)
 (λC_op.λR_op.⊖(eqc ? R_op (zeroc ?))).

(* nulla *)
ndefinition execute_NOP ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 Some ? (pair … s cur_pc).

(* A = (mk_byte8 (b8l A) (b8h A)) *)
(* cioe' swap del nibble alto/nibble basso di A *)
ndefinition execute_NSA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 match get_acc_8_low_reg … s with [ mk_comp_num ah al ⇒
  (* A = (mk_byte8 (b8l A) (b8h A)) *)
  Some ? (pair … (set_acc_8_low_reg … s 〈al,ah〉) cur_pc) ].

(* A = A | M *)
ndefinition execute_ORA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_AND_BIT_EOR_ORA_aux … s cur_pc i true (orc ?).

(* push A *)
ndefinition execute_PSHA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (aux_push … s (get_acc_8_low_reg … s))
  (λs_tmp1.Some ? (pair … s_tmp1 cur_pc)).

(* push H *)
ndefinition execute_PSHH ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (get_indX_8_high_reg … s)
  (λH_op.opt_map … (aux_push … s H_op)
   (λs_tmp1.Some ? (pair … s_tmp1 cur_pc))).

(* push X *)
ndefinition execute_PSHX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (get_indX_8_low_reg … s)
  (λH_op.opt_map … (aux_push … s H_op)
   (λs_tmp1.Some ? (pair … s_tmp1 cur_pc))).

(* pop A *)
ndefinition execute_PULA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (aux_pop … s)
  (λS_and_A.match S_and_A with [ pair s_tmp1 A_op ⇒
   Some ? (pair … (set_acc_8_low_reg … s_tmp1 A_op) cur_pc) ]).

(* pop H *)
ndefinition execute_PULH ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (aux_pop … s)
  (λS_and_H.match S_and_H with [ pair s_tmp1 H_op ⇒
   opt_map … (set_indX_8_high_reg … s_tmp1 H_op)
    (λs_tmp2.Some ? (pair … s_tmp2 cur_pc))]).

(* pop X *)
ndefinition execute_PULX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (aux_pop … s)
  (λS_and_X.match S_and_X with [ pair s_tmp1 X_op ⇒
   opt_map … (set_indX_8_low_reg … s_tmp1 X_op)
    (λs_tmp2.Some ? (pair … s_tmp2 cur_pc))]).

(* M = C' <- rcl M <- C *)
ndefinition execute_ROL ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_ASL_ASR_LSR_ROL_ROR_aux … s cur_pc i (rclc ?).

(* M = C -> rcr M -> C' *)
ndefinition execute_ROR ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_ASL_ASR_LSR_ROL_ROR_aux … s cur_pc i (rcrc ?).

(* SP = 0xuuFF *)
(* lascia inalterato il byte superiore di SP *)
ndefinition execute_RSP ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (get_sp_reg … s)
  (λSP_op.match SP_op with [ mk_comp_num sph spl ⇒
   opt_map … (set_sp_reg … s 〈sph:〈xF,xF〉〉)
    (λs_tmp.Some ? (pair … s_tmp cur_pc))]).

(* return from interrupt *)
ndefinition execute_RTI ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 (* pop (CCR) *)
 opt_map … (aux_pop … s)
  (λS_and_CCR.match S_and_CCR with [ pair s_tmp1 CCR_op ⇒
   let s_tmp2 ≝ aux_set_CCR … s_tmp1 CCR_op in
   (* pop (A) *)
   opt_map … (aux_pop … s_tmp2)
    (λS_and_A.match S_and_A with [ pair s_tmp3 A_op ⇒
     let s_tmp4 ≝ set_acc_8_low_reg … s_tmp3 A_op in
     (* pop (X) *)
     opt_map … (aux_pop … s_tmp4)
      (λS_and_X.match S_and_X with [ pair s_tmp5 X_op ⇒
       opt_map … (set_indX_8_low_reg … s_tmp5 X_op)
        (* pop (PC high) *)
        (λs_tmp6.opt_map … (aux_pop … s_tmp6)
         (λS_and_PCH.match S_and_PCH with [ pair s_tmp7 PCH_op ⇒
          (* pop (PC low) *)
          opt_map … (aux_pop … s_tmp7)
           (λS_and_PCL.match S_and_PCL with [ pair s_tmp8 PCL_op ⇒
            Some ? (pair … s_tmp8 〈PCH_op:PCL_op〉)])]))])])]).

(* return from subroutine *)
(* HC05/HC08/HCS08 si appoggia allo stack, RS08 si appoggia a SPC *)
ndefinition execute_RTS ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 let aux ≝
  (* pop (PC high) *)
  opt_map … (aux_pop … s)
   (λS_and_PCH.match S_and_PCH with [ pair s_tmp1 PCH_op ⇒
    (* pop (PC low) *)
    opt_map … (aux_pop … s_tmp1)
     (λS_and_PCL.match S_and_PCL with [ pair s_tmp2 PCL_op ⇒
      Some ? (pair … s_tmp2 〈PCH_op:PCL_op〉)])])
 in match m with
  [ HC05 ⇒ aux | HC08 ⇒ aux | HCS08 ⇒ aux
  | RS08 ⇒
   (* new_pc = SPC *)
   opt_map … (get_spc_reg … s)
    (λSPC_op.Some ? (pair … s SPC_op))
  | _ ⇒ None ?
  ].

(* A = A - M - C *)
ndefinition execute_SBC ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_CMP_SBC_SUB_aux … s cur_pc i true
 (λC_op.λA_op.λM_op.match plusc_dc_dc ? false A_op (complc ? M_op) with
  [ pair resc resb ⇒ match C_op with
   [ true ⇒ plusc_dc_dc ? false resb 〈xF,xF〉
   | false ⇒ pair … resc resb ]]).

(* C = 1 *)
ndefinition execute_SEC ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 Some ? (pair … (set_c_flag … s true) cur_pc).

(* I = 1 *)
ndefinition execute_SEI ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (set_i_flag … s true)
  (λs_tmp.Some ? (pair … s_tmp cur_pc)).

(* swap SPCh,A *)
(* senso: nell'RS08 SPC non e' accessibile direttamente e come si possono
          fare subroutine annidate se RA (return address) e' salvato sempre in SPC?
          occore accedere a SPC e salvarne il contenuto *)
ndefinition execute_SHA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (get_spc_reg … s)
  (λSPC_op.opt_map … (set_spc_reg … s 〈(get_acc_8_low_reg … s):(cnL ? SPC_op)〉)
   (λs_tmp1.Some ? (pair … (set_acc_8_low_reg … s_tmp1 (cnH ? SPC_op)) cur_pc))).

(* swap SPCl,A *)
(* senso: nell'RS08 SPC non e' accessibile direttamente e come si possono
          fare subroutine annidate se RA (return address) e' salvato sempre in SPC?
          occore accedere a SPC e salvarne il contenuto *)
ndefinition execute_SLA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (get_spc_reg … s)
  (λSPC_op.opt_map … (set_spc_reg … s 〈(cnH ? SPC_op):(get_acc_8_low_reg … s)〉)
   (λs_tmp1.Some ? (pair … (set_acc_8_low_reg … s_tmp1 (cnL ? SPC_op)) cur_pc))).

(* M = A *)
ndefinition execute_STA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 (* M = A *)
 let A_op ≝ (get_acc_8_low_reg … s) in
 opt_map … (multi_mode_writeb … s cur_pc auxMode_ok i A_op)
  (λS_op_and_PC.match S_op_and_PC with
   [ pair s_tmp1 new_pc ⇒
   (* Z = nA7&nA6&nA5&nA4&nA3&nA2&nA1&nA0 *)
   let s_tmp2 ≝ set_zflb … s_tmp1 A_op in
   (* N = A7 *)
   let s_tmp3 ≝ set_nflb … s_tmp2 A_op in
   (* V = 0 *)
   let s_tmp4 ≝ setweak_v_flag … s_tmp3 false in
   (* newpc = nextpc *)
   Some ? (pair … s_tmp4 new_pc) ]).

(* M = H:X *)
ndefinition execute_STHX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 (* M = H:X *)
 opt_map … (get_indX_16_reg … s)
  (λX_op.opt_map … (multi_mode_writew … s cur_pc i X_op)
   (λS_op_and_PC.match S_op_and_PC with
    [ pair s_tmp1 new_pc ⇒
     (* Z = nR15&nR14&nR13nR12&nR11&nR10&nR9&nR8nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
     let s_tmp2 ≝ set_zflw … s_tmp1 X_op in
     (* N = R15 *)
     let s_tmp3 ≝ set_nflw … s_tmp2 X_op in
     (* V = 0 *)
     let s_tmp4 ≝ setweak_v_flag … s_tmp3 false in
     (* newpc = nextpc *)
      Some ? (pair … s_tmp4 new_pc) ])).

(* I = 0 *)
ndefinition execute_STOP ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 Some ? (pair … (setweak_i_flag … s false) cur_pc).

(* M = X *)
ndefinition execute_STX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 (* M = X *)
 opt_map … (get_indX_8_low_reg … s)
  (λX_op.opt_map … (multi_mode_writeb … s cur_pc auxMode_ok i X_op)
   (λS_op_and_PC.match S_op_and_PC with
    [ pair s_tmp1 new_pc ⇒
     (* Z = nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
     let s_tmp2 ≝ set_zflb … s_tmp1 X_op in
     (* N = R7 *)
     let s_tmp3 ≝ set_nflb … s_tmp2 X_op in
     (* V = 0 *)
     let s_tmp4 ≝ setweak_v_flag … s_tmp3 false in
     (* newpc = nextpc *)
     Some ? (pair … s_tmp4 new_pc) ])).

(* A = A - M *)
ndefinition execute_SUB ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 execute_CMP_SBC_SUB_aux … s cur_pc i true (λC_op.λA_op.λM_op.plusc_dc_dc ? false A_op (complc ? M_op)).

(* software interrupt *)
ndefinition execute_SWI ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 (* indirizzo da cui caricare il nuovo pc *)
 let vector ≝ get_pc_reg … (set_pc_reg … s 〈〈xF,xF〉:〈xF,xC〉〉) in
 (* push (cur_pc low) *)
 opt_map … (aux_push … s (cnL ? cur_pc))
  (* push (cur_pc high *)
  (λs_tmp1.opt_map … (aux_push … s_tmp1 (cnH ? cur_pc))
   (λs_tmp2.opt_map … (get_indX_8_low_reg … s_tmp2)
    (* push (X) *)
    (λX_op.opt_map … (aux_push … s_tmp2 X_op)
     (* push (A) *)
     (λs_tmp3.opt_map … (aux_push … s_tmp3 (get_acc_8_low_reg … s_tmp3))
      (* push (CCR) *)
      (λs_tmp4.opt_map … (aux_push … s_tmp4 (aux_get_CCR … s_tmp4))
       (* I = 1 *)
       (λs_tmp5.opt_map … (set_i_flag … s_tmp5 true)
        (* load from vector high *)
        (λs_tmp6.opt_map … (memory_filter_read … s_tmp6 vector)
         (* load from vector low *)
         (λaddrh.opt_map … (memory_filter_read … s_tmp6 (succc ? vector))
          (* newpc = [vector] *)
          (λaddrl.Some ? (pair … s_tmp6 〈addrh:addrl〉)))))))))).

(* flags = A *)
ndefinition execute_TAP ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 Some ? (pair … (aux_set_CCR … s (get_acc_8_low_reg … s)) cur_pc). 

(* X = A *)
ndefinition execute_TAX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (set_indX_8_low_reg … s (get_acc_8_low_reg … s))
  (λs_tmp.Some ? (pair … s_tmp cur_pc)).

(* A = flags *)
ndefinition execute_TPA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 Some ? (pair … (set_acc_8_low_reg … s (aux_get_CCR … s)) cur_pc).

(* flags = M - 0 *)
(* implementata senza richiamare la sottrazione, la modifica dei flag
   e' immediata *)
ndefinition execute_TST ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (multi_mode_loadb … s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ triple s_tmp1 M_op new_pc ⇒
    (* Z = nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
    let s_tmp2 ≝ set_zflb … s_tmp1 M_op in
    (* N = R7 *) 
    let s_tmp3 ≝ set_nflb … s_tmp2 M_op in
    (* V = 0 *) 
    let s_tmp4 ≝ setweak_v_flag … s_tmp3 false in
    (* newpc = nextpc *)
    Some ? (pair … s_tmp4 new_pc) ]).

(* H:X = SP + 1 *)
ndefinition execute_TSX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (get_sp_reg … s )
  (λSP_op.opt_map … (set_indX_16_reg … s (succc ? SP_op))
   (* H:X = SP + 1 *)
   (λs_tmp.Some ? (pair … s_tmp cur_pc))).

(* A = X *)
ndefinition execute_TXA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (get_indX_8_low_reg … s)
  (λX_op.Some ? (pair … (set_acc_8_low_reg … s X_op) cur_pc)).

(* SP = H:X - 1 *)
ndefinition execute_TXS ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 opt_map … (get_indX_16_reg … s )
  (λX_op.opt_map … (set_sp_reg … s (predc ? X_op))
   (* SP = H:X - 1 *)
   (λs_tmp.Some ? (pair … s_tmp cur_pc))).

(* I = 0 *)
ndefinition execute_WAIT ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 Some ? (pair … (setweak_i_flag … s false) cur_pc).

(* raccordo *)
ndefinition Freescale_execute_any ≝
λps:Freescale_pseudo.match ps with
  [ ADC    ⇒ execute_ADC    (* add with carry *)
  | ADD    ⇒ execute_ADD    (* add *)
  | AIS    ⇒ execute_AIS    (* add immediate to SP *)
  | AIX    ⇒ execute_AIX    (* add immediate to X *)
  | AND    ⇒ execute_AND    (* and *)
  | ASL    ⇒ execute_ASL    (* aritmetic shift left *)
  | ASR    ⇒ execute_ASR    (* aritmetic shift right *)
  | BCC    ⇒ execute_BCC    (* branch if C=0 *)
  | BCLRn  ⇒ execute_BCLRn  (* clear bit n *)
  | BCS    ⇒ execute_BCS    (* branch if C=1 *)
  | BEQ    ⇒ execute_BEQ    (* branch if Z=1 *)
  | BGE    ⇒ execute_BGE    (* branch if N⊙V=0 (great or equal) *)
  | BGND   ⇒ execute_BGND   (* !!background mode!!*)
  | BGT    ⇒ execute_BGT    (* branch if Z|N⊙V=0 clear (great) *)
  | BHCC   ⇒ execute_BHCC   (* branch if H=0 *)
  | BHCS   ⇒ execute_BHCS   (* branch if H=1 *)
  | BHI    ⇒ execute_BHI    (* branch if C|Z=0, (higher) *)
  | BIH    ⇒ execute_BIH    (* branch if nIRQ=1 *)
  | BIL    ⇒ execute_BIL    (* branch if nIRQ=0 *)
  | BIT    ⇒ execute_BIT    (* flag = and (bit test) *)
  | BLE    ⇒ execute_BLE    (* branch if Z|N⊙V=1 (less or equal) *)
  | BLS    ⇒ execute_BLS    (* branch if C|Z=1 (lower or same) *)
  | BLT    ⇒ execute_BLT    (* branch if N⊙1=1 (less) *)
  | BMC    ⇒ execute_BMC    (* branch if I=0 (interrupt mask clear) *)
  | BMI    ⇒ execute_BMI    (* branch if N=1 (minus) *)
  | BMS    ⇒ execute_BMS    (* branch if I=1 (interrupt mask set) *)
  | BNE    ⇒ execute_BNE    (* branch if Z=0 *)
  | BPL    ⇒ execute_BPL    (* branch if N=0 (plus) *)
  | BRA    ⇒ execute_BRA    (* branch always *)
  | BRCLRn ⇒ execute_BRCLRn (* branch if bit n clear *)
  | BRN    ⇒ execute_BRN    (* branch never (nop) *)
  | BRSETn ⇒ execute_BRSETn (* branch if bit n set *)
  | BSETn  ⇒ execute_BSETn  (* set bit n *)
  | BSR    ⇒ execute_BSR    (* branch to subroutine *)
  | CBEQA  ⇒ execute_CBEQA  (* compare (A) and BEQ *)
  | CBEQX  ⇒ execute_CBEQX  (* compare (X) and BEQ *)
  | CLC    ⇒ execute_CLC    (* C=0 *)
  | CLI    ⇒ execute_CLI    (* I=0 *)
  | CLR    ⇒ execute_CLR    (* operand=0 *)
  | CMP    ⇒ execute_CMP    (* flag = sub (compare A) *)
  | COM    ⇒ execute_COM    (* not (1 complement) *)
  | CPHX   ⇒ execute_CPHX   (* flag = sub (compare H:X) *)
  | CPX    ⇒ execute_CPX    (* flag = sub (compare X) *)
  | DAA    ⇒ execute_DAA    (* decimal adjust A *)
  | DBNZ   ⇒ execute_DBNZ   (* dec and BNE *)
  | DEC    ⇒ execute_DEC    (* operand=operand-1 (decrement) *)
  | DIV    ⇒ execute_DIV    (* div *)
  | EOR    ⇒ execute_EOR    (* xor *)
  | INC    ⇒ execute_INC    (* operand=operand+1 (increment) *)
  | JMP    ⇒ execute_JMP    (* jmp word [operand] *)
  | JSR    ⇒ execute_JSR    (* jmp to subroutine *)
  | LDA    ⇒ execute_LDA    (* load in A *)
  | LDHX   ⇒ execute_LDHX   (* load in H:X *)
  | LDX    ⇒ execute_LDX    (* load in X *)
  | LSR    ⇒ execute_LSR    (* logical shift right *)
  | MOV    ⇒ execute_MOV    (* move *)
  | MUL    ⇒ execute_MUL    (* mul *)
  | NEG    ⇒ execute_NEG    (* neg (2 complement) *)
  | NOP    ⇒ execute_NOP    (* nop *)
  | NSA    ⇒ execute_NSA    (* nibble swap A (al:ah <- ah:al) *)
  | ORA    ⇒ execute_ORA    (* or *)
  | PSHA   ⇒ execute_PSHA   (* push A *)
  | PSHH   ⇒ execute_PSHH   (* push H *)
  | PSHX   ⇒ execute_PSHX   (* push X *)
  | PULA   ⇒ execute_PULA   (* pop A *)
  | PULH   ⇒ execute_PULH   (* pop H *)
  | PULX   ⇒ execute_PULX   (* pop X *)
  | ROL    ⇒ execute_ROL    (* rotate left *)
  | ROR    ⇒ execute_ROR    (* rotate right *)
  | RSP    ⇒ execute_RSP    (* reset SP (0x00FF) *)
  | RTI    ⇒ execute_RTI    (* return from interrupt *)
  | RTS    ⇒ execute_RTS    (* return from subroutine *)
  | SBC    ⇒ execute_SBC    (* sub with carry*)
  | SEC    ⇒ execute_SEC    (* C=1 *)
  | SEI    ⇒ execute_SEI    (* I=1 *)
  | SHA    ⇒ execute_SHA    (* swap spc_high,A *)
  | SLA    ⇒ execute_SLA    (* swap spc_low,A *)
  | STA    ⇒ execute_STA    (* store from A *)
  | STHX   ⇒ execute_STHX   (* store from H:X *)
  | STOP   ⇒ execute_STOP   (* !!stop mode!! *)
  | STX    ⇒ execute_STX    (* store from X *)
  | SUB    ⇒ execute_SUB    (* sub *)
  | SWI    ⇒ execute_SWI    (* software interrupt *)
  | TAP    ⇒ execute_TAP    (* flag=A (transfer A to process status byte *)
  | TAX    ⇒ execute_TAX    (* X=A (transfer A to X) *)
  | TPA    ⇒ execute_TPA    (* A=flag (transfer process status byte to A) *)
  | TST    ⇒ execute_TST    (* flag = sub (test) *)
  | TSX    ⇒ execute_TSX    (* X:H=SP (transfer SP to H:X) *)
  | TXA    ⇒ execute_TXA    (* A=X (transfer X to A) *)
  | TXS    ⇒ execute_TXS    (* SP=X:H (transfer H:X to SP) *)
  | WAIT   ⇒ execute_WAIT   (* !!wait mode!!*)
  ].

(* stati speciali di esecuzione *)
ndefinition Freescale_check_susp ≝
λps:Freescale_pseudo.match ps with
 [ BGND ⇒ Some ? BGND_MODE
 | STOP ⇒ Some ? STOP_MODE
 | WAIT ⇒ Some ? WAIT_MODE
 | _ ⇒ None ?
 ].

(* istruzioni speciali per skip *)
ndefinition Freescale_check_skip ≝
λps:Freescale_pseudo.false.

(* motiplicatore del ciclo di durata *)
ndefinition Freescale_clk_mult ≝
λm,t.λs:any_status m t.nat1.
