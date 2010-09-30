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
(*                           Progetto FreeScale                           *)
(*                                                                        *)
(* Sviluppato da:                                                         *)
(*   Cosimo Oliboni, oliboni@cs.unibo.it                                  *)
(*                                                                        *)
(* Questo materiale fa parte della tesi:                                  *)
(*   "Formalizzazione Interattiva dei Microcontroller a 8bit FreeScale"   *)
(*                                                                        *)
(*                    data ultima modifica 15/11/2007                     *)
(* ********************************************************************** *)

include "freescale/load_write.ma".

(* ************************************************ *)
(* LOGICHE AUSILIARE CHE ACCOMUNANO PIU' OPERAZIONI *)
(* ************************************************ *)

(* NB: dentro il codice i commenti cercano di spiegare la logica
       secondo quanto riportato dalle specifiche delle mcu *)

(* NB: notare che tranne nei casi in cui PC viene modificato esplicitamente
       il suo avanzamento viene delegato totalmente agli strati inferiori
       I) avanzamento dovuto al decode degli op (fetch)
       II) avanzamento dovuto al caricamento degli argomenti (multi_mode_load/write)
       la modifica effettiva avviene poi centralizzata in tick *)

(* A = [true] fAMC(A,M,C), [false] A *)
(* cioe' in caso di false l'operazione viene eseguita ma modifica solo i flag *)
(* fAMC e' la logica da applicare: somma con/senza carry *)
definition execute_ADC_ADD_aux ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.λsetflag:bool.
λfAMC:byte8 → byte8 → bool → Prod byte8 bool.
 opt_map ?? (multi_mode_load true m t s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ tripleT s_tmp1 M_op new_pc ⇒
    let A_op ≝ get_acc_8_low_reg m t s_tmp1 in
    match fAMC A_op M_op (get_c_flag m t s_tmp1) with
     [ pair R_op carry ⇒
      let A7 ≝ MSB_b8 A_op in let M7 ≝ MSB_b8 M_op in let R7 ≝ MSB_b8 R_op in
      let A3 ≝ MSB_ex (b8l A_op) in let M3 ≝ MSB_ex (b8l M_op) in let R3 ≝ MSB_ex (b8l R_op) in
      (* A = [true] fAMC(A,M,C), [false] A *)
      let s_tmp2 ≝ match setflag with [ true ⇒ set_acc_8_low_reg m t s_tmp1 R_op | false ⇒ s_tmp1 ] in
      (* Z = nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
      let s_tmp3 ≝ set_z_flag m t s_tmp2 (eq_b8 R_op 〈x0,x0〉) in
      (* C = A7&M7 | M7&nR7 | nR7&A7 *)
      let s_tmp4 ≝ set_c_flag m t s_tmp3 ((A7⊗M7) ⊕ (M7⊗(⊖R7)) ⊕ ((⊖R7)⊗A7)) in
      (* N = R7 *)
      let s_tmp5 ≝ setweak_n_flag m t s_tmp4 R7 in
      (* H = A3&M3 | M3&nR3 | nR3&A3 *)
      let s_tmp6 ≝ setweak_h_flag m t s_tmp5 ((A3⊗M3) ⊕ (M3⊗(⊖R3)) ⊕ ((⊖R3)⊗A3)) in
      (* V = A7&M7&nR7 | nA7&nM7&R7 *)
      let s_tmp7 ≝ setweak_v_flag m t s_tmp6 ((A7⊗M7⊗(⊖R7)) ⊕ ((⊖A7)⊗(⊖M7)⊗R7)) in
      (* newpc = nextpc *)
      Some ? (pair ?? s_tmp7 new_pc) ]]).

(* A = [true] fAM(A,M), [false] A *)
(* cioe' in caso di false l'operazione viene eseguita ma modifica solo i flag *)
(* fAM e' la logica da applicare: and/xor/or *)
definition execute_AND_BIT_EOR_ORA_aux ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.λsetflag:bool.
λfAM:byte8 → byte8 → byte8.
 opt_map ?? (multi_mode_load true m t s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ tripleT s_tmp1 M_op new_pc ⇒
    let R_op ≝ fAM (get_acc_8_low_reg m t s_tmp1) M_op in
    (* A = [true] fAM(A,M), [false] A *) 
    let s_tmp2 ≝ match setflag with [ true ⇒ set_acc_8_low_reg m t s_tmp1 R_op | false ⇒ s_tmp1 ] in
    (* Z = nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
    let s_tmp3 ≝ set_z_flag m t s_tmp2 (eq_b8 R_op 〈x0,x0〉) in
    (* N = R7 *) 
    let s_tmp4 ≝ setweak_n_flag m t s_tmp3 (MSB_b8 R_op) in
    (* V = 0 *) 
    let s_tmp5 ≝ setweak_v_flag m t s_tmp4 false in
    (* newpc = nextpc *)
    Some ? (pair ?? s_tmp5 new_pc) ]).

(* M = fMC(M,C) *)
(* fMC e' la logica da applicare: rc_/ro_/sh_ *)
definition execute_ASL_ASR_LSR_ROL_ROR_aux ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
λfMC:byte8 → bool → Prod byte8 bool.
 opt_map ?? (multi_mode_load true m t s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ tripleT s_tmp1 M_op _ ⇒
    match fMC M_op (get_c_flag m t s_tmp1) with [ pair R_op carry ⇒
    (* M = fMC(M,C) *)
    opt_map ?? (multi_mode_write true m t s_tmp1 cur_pc i R_op)
     (λS_PC.match S_PC with
      [ pair s_tmp2 new_pc ⇒
      (* C = carry *)
      let s_tmp3 ≝ set_c_flag m t s_tmp2 carry in
      (* Z = nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
      let s_tmp4 ≝ set_z_flag m t s_tmp3 (eq_b8 R_op 〈x0,x0〉) in
      (* N = R7 *)
      let s_tmp5 ≝ setweak_n_flag m t s_tmp4 (MSB_b8 R_op) in
      (* V = R7 ⊙ carry *)
      let s_tmp6 ≝ setweak_v_flag m t s_tmp5 ((MSB_b8 R_op) ⊙ carry) in
      (* newpc = nextpc *)
      Some ? (pair ?? s_tmp6 new_pc) ])]]).

(* estensione del segno byte → word *)
definition byte_extension ≝
λb:byte8.〈match MSB_b8 b with [ true ⇒ 〈xF,xF〉 | false ⇒ 〈x0,x0〉 ]:b〉.

(* branch con byte+estensione segno *)
definition branched_pc ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λb:byte8.
 get_pc_reg m t (set_pc_reg m t s (plus_w16nc cur_pc (byte_extension b))).

(* if COND=1 branch *)
(* tutti i branch calcoleranno la condizione e la passeranno qui *)
definition execute_any_BRANCH ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.λfCOND:bool.
 opt_map ?? (multi_mode_load true m t s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ tripleT s_tmp1 M_op new_pc ⇒
    (* if true, branch *) 
    match fCOND with
     (* newpc = nextpc + rel *)
     [ true ⇒ Some ? (pair ?? s_tmp1 (branched_pc m t s_tmp1 new_pc M_op))
     (* newpc = nextpc *)
     | false ⇒ Some ? (pair ?? s_tmp1 new_pc) ]]).

(* Mn = filtered optval *) 
(* il chiamante passa 0x00 per azzerare, 0xFF per impostare il bit di M *)
definition execute_BCLRn_BSETn_aux ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.λoptval:byte8.
 (* Mn = filtered optval *)
 opt_map ?? (multi_mode_write true m t s cur_pc i optval)
  (λS_PC.match S_PC with
   (* newpc = nextpc *)
   [ pair s_tmp1 new_pc ⇒ Some ? (pair ?? s_tmp1 new_pc) ]).

(* if COND(Mn) branch *)
(* il chiamante passa la logica da testare (0x00,¬0x00) e poi si salta *)
definition execute_BRCLRn_BRSETn_aux ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.λfCOND:byte8 → bool.
 opt_map ?? (multi_mode_load false m t s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ tripleT s_tmp1 M_op new_pc ⇒ match M_op with
    [ mk_word16 MH_op ML_op ⇒
     (* if COND(Mn) branch *)
     match fCOND MH_op with
      (* newpc = nextpc + rel *)
      [ true ⇒ Some ? (pair ?? s_tmp1 (branched_pc m t s_tmp1 new_pc ML_op))
      (* newpc = nextpc *)
      | false ⇒ Some ? (pair ?? s_tmp1 new_pc) ]]]).

(* M = fM(M) *)
(* fM e' la logica da applicare: not/neg/++/-- *)
definition execute_COM_DEC_INC_NEG_aux ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
λfM:byte8 → byte8.λfV:bool → bool → bool.λfC:bool → byte8 → bool.
 opt_map ?? (multi_mode_load true m t s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ tripleT s_tmp1 M_op _ ⇒
    let R_op ≝ fM M_op in
    (* M = fM(M) *)
    opt_map ?? (multi_mode_write true m t s_tmp1 cur_pc i R_op)
     (λS_PC.match S_PC with
      [ pair s_tmp2 new_pc ⇒
      (* C = fCR (C,R) *)
      let s_tmp3 ≝ set_c_flag m t s_tmp2 (fC (get_c_flag m t s_tmp2) R_op) in
      (* Z = nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
      let s_tmp4 ≝ set_z_flag m t s_tmp3 (eq_b8 R_op 〈x0,x0〉) in
      (* N = R7 *)
      let s_tmp5 ≝ setweak_n_flag m t s_tmp4 (MSB_b8 R_op) in
      (* V = fV (M7,R7) *)
      let s_tmp6 ≝ setweak_v_flag m t s_tmp5 (fV (MSB_b8 M_op) (MSB_b8 R_op)) in
      (* newpc = nextpc *)
      Some ? (pair ?? s_tmp6 new_pc) ])]).

(* A = [true] fAMC(A,M,C), [false] A *)
(* cioe' in caso di false l'operazione viene eseguita ma modifica solo i flag *)
(* fAMC e' la logica da applicare: sottrazione con/senza carry *)
definition execute_SBC_SUB_aux ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.λsetflag:bool.
λfAMC:byte8 → byte8 → bool → Prod byte8 bool.
 opt_map ?? (multi_mode_load true m t s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ tripleT s_tmp1 M_op new_pc ⇒
    let A_op ≝ get_acc_8_low_reg m t s_tmp1 in
    match fAMC A_op M_op (get_c_flag m t s_tmp1) with
     [ pair R_op carry ⇒
      let A7 ≝ MSB_b8 A_op in let M7 ≝ MSB_b8 M_op in let R7 ≝ MSB_b8 R_op in
      (* A = [true] fAMC(A,M,C), [false] A *)
      let s_tmp2 ≝ match setflag with [ true ⇒ set_acc_8_low_reg m t s_tmp1 R_op | false ⇒ s_tmp1 ] in
      (* Z = nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
      let s_tmp3 ≝ set_z_flag m t s_tmp2 (eq_b8 R_op 〈x0,x0〉) in
      (* C = nA7&M7 | M7&R7 | R7&nA7 *)
      let s_tmp4 ≝ set_c_flag m t s_tmp3 (((⊖A7)⊗M7) ⊕ (M7⊗R7) ⊕ (R7⊗(⊖A7))) in
      (* N = R7 *) 
      let s_tmp5 ≝ setweak_n_flag m t s_tmp4 R7 in
      (* V = A7&nM7&nR7 | nA7&M7&R7 *)
      let s_tmp6 ≝ setweak_v_flag m t s_tmp5 ((A7⊗(⊖M7)⊗(⊖R7)) ⊕ ((⊖A7)⊗M7⊗R7)) in
      (* newpc = nextpc *)
      Some ? (pair ?? s_tmp6 new_pc) ]]).

(* il classico push *)
definition aux_push ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval:byte8.
 opt_map ?? (get_sp_reg m t s)
  (* [SP] = val *)
  (λSP_op.opt_map ?? (memory_filter_write m t s SP_op val)
   (* SP -- *)
   (λs_tmp1.opt_map ?? (set_sp_reg m t s_tmp1 (pred_w16 SP_op))
    (λs_tmp2.Some ? s_tmp2))).

(* il classico pop *)
(* NB: l'incremento di SP deve essere filtrato dalla ALU, quindi get(set(SP)) *)
definition aux_pop ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 opt_map ?? (get_sp_reg m t s)
  (* SP ++ *)
  (λSP_op.opt_map ?? (set_sp_reg m t s (succ_w16 SP_op))
   (λs_tmp1.opt_map ?? (get_sp_reg m t s_tmp1)
    (* val = [SP] *)
    (λSP_op'.opt_map ?? (memory_filter_read m t s_tmp1 SP_op')
     (λval.Some ? (pair ?? s_tmp1 val))))).

(* CCR corrisponde a V11HINZC e cmq 1 se un flag non esiste *)
(* i flag mantengono posizione costante nelle varie ALU, e se non sono
   implementati corrispondono a 1 *)
definition aux_get_CCR ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
let V_comp ≝ match get_v_flag m t s with
 [ None ⇒ 〈x8,x0〉  | Some V_val ⇒ match V_val with [ true ⇒ 〈x8,x0〉  | false ⇒ 〈x0,x0〉 ]] in
let H_comp ≝ match get_h_flag m t s with
 [ None ⇒ 〈x1,x0〉  | Some H_val ⇒ match H_val with [ true ⇒ 〈x1,x0〉  | false ⇒ 〈x0,x0〉 ]] in
let I_comp ≝ match get_i_flag m t s with
 [ None ⇒ 〈x0,x8〉  | Some I_val ⇒ match I_val with [ true ⇒ 〈x0,x8〉  | false ⇒ 〈x0,x0〉 ]] in
let N_comp ≝ match get_n_flag m t s with
 [ None ⇒ 〈x0,x4〉  | Some N_val ⇒ match N_val with [ true ⇒ 〈x0,x4〉  | false ⇒ 〈x0,x0〉 ]] in
let Z_comp ≝ match get_z_flag m t s with
 [ true ⇒ 〈x0,x2〉  | false ⇒ 〈x0,x0〉 ] in
let C_comp ≝ match get_c_flag m t s with
 [ true ⇒ 〈x0,x1〉  | false ⇒ 〈x0,x0〉 ] in
or_b8 〈x6,x0〉 (or_b8 V_comp (or_b8 H_comp (or_b8 I_comp (or_b8 N_comp (or_b8 Z_comp C_comp))))).

(* CCR corrisponde a V11HINZC *)
(* i flag mantengono posizione costante nelle varie ALU, e se non sono
   implementati si puo' usare tranquillamente setweak *)
definition aux_set_CCR ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λCCR:byte8.
 let s_tmp1 ≝ set_c_flag m t s          (eq_b8 〈x0,x1〉 (and_b8 〈x0,x1〉 CCR)) in
 let s_tmp2 ≝ set_z_flag m t s_tmp1     (eq_b8 〈x0,x2〉 (and_b8 〈x0,x2〉 CCR)) in
 let s_tmp3 ≝ setweak_n_flag m t s_tmp2 (eq_b8 〈x0,x4〉 (and_b8 〈x0,x4〉 CCR)) in
 let s_tmp4 ≝ setweak_i_flag m t s_tmp3 (eq_b8 〈x0,x8〉 (and_b8 〈x0,x8〉 CCR)) in
 let s_tmp5 ≝ setweak_h_flag m t s_tmp4 (eq_b8 〈x1,x0〉 (and_b8 〈x1,x0〉 CCR)) in
 let s_tmp6 ≝ setweak_v_flag m t s_tmp5 (eq_b8 〈x8,x0〉 (and_b8 〈x8,x0〉 CCR)) in
 s_tmp6.

(* **************** *)
(* LOGICA DELLA ALU *)
(* **************** *)

(* A = A + M + C *)
definition execute_ADC ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_ADC_ADD_aux m t s i cur_pc true (λA_op.λM_op.λC_op.plus_b8 A_op M_op C_op).

(* A = A + M *)
definition execute_ADD ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_ADC_ADD_aux m t s i cur_pc true (λA_op.λM_op.λC_op.plus_b8 A_op M_op false).

(* SP += extended M *)
definition execute_AIS ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (multi_mode_load true m t s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ tripleT s_tmp1 M_op new_pc ⇒
   opt_map ?? (get_sp_reg m t s_tmp1)
    (* SP += extended M *)
    (λSP_op.opt_map ?? (set_sp_reg m t s_tmp1 (plus_w16nc SP_op (byte_extension M_op)))
     (λs_tmp2.Some ? (pair ?? s_tmp2 new_pc))) ]).

(* H:X += extended M *)
definition execute_AIX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (multi_mode_load true m t s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ tripleT s_tmp1 M_op new_pc ⇒
   opt_map ?? (get_indX_16_reg m t s_tmp1)
    (* H:X += extended M *)
    (λHX_op.opt_map ?? (set_indX_16_reg m t s_tmp1 (plus_w16nc HX_op (byte_extension M_op)))
     (λs_tmp2.Some ? (pair ?? s_tmp2 new_pc))) ]).

(* A = A & M *)
definition execute_AND ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_AND_BIT_EOR_ORA_aux m t s i cur_pc true and_b8.

(* M = C' <- rcl M <- 0 *)
definition execute_ASL ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_ASL_ASR_LSR_ROL_ROR_aux m t s i cur_pc (λM_op.λC_op.rcl_b8 M_op false).

(* M = M7 -> rcr M -> C' *)
definition execute_ASR ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_ASL_ASR_LSR_ROL_ROR_aux m t s i cur_pc (λM_op.λC_op.rcr_b8 M_op (MSB_b8 M_op)).

(* if C=0, branch *) 
definition execute_BCC ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_any_BRANCH m t s i cur_pc (⊖(get_c_flag m t s)).

(* Mn = 0 *)
definition execute_BCLRn ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_BCLRn_BSETn_aux m t s i cur_pc 〈x0,x0〉.

(* if C=1, branch *) 
definition execute_BCS ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_any_BRANCH m t s i cur_pc (get_c_flag m t s).

(* if Z=1, branch *)
definition execute_BEQ ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_any_BRANCH m t s i cur_pc (get_z_flag m t s).

(* if N⊙V=0, branch *)
definition execute_BGE ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (get_n_flag m t s)
  (λN_op.opt_map ?? (get_v_flag m t s)
   (λV_op.execute_any_BRANCH m t s i cur_pc (⊖(N_op ⊙ V_op)))).

(* BGND mode *)
definition execute_BGND ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 Some ? (pair ?? s cur_pc).

(* if Z|N⊙V=0, branch *)
definition execute_BGT ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (get_n_flag m t s)
  (λN_op.opt_map ?? (get_v_flag m t s)
   (λV_op.execute_any_BRANCH m t s i cur_pc (⊖((get_z_flag m t s) ⊕ (N_op ⊙ V_op))))).

(* if H=0, branch *)
definition execute_BHCC ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (get_h_flag m t s)
  (λH_op.execute_any_BRANCH m t s i cur_pc (⊖H_op)).

(* if H=1, branch *)
definition execute_BHCS ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (get_h_flag m t s)
  (λH_op.execute_any_BRANCH m t s i cur_pc H_op).

(* if C|Z=0, branch *)
definition execute_BHI ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_any_BRANCH m t s i cur_pc (⊖((get_c_flag m t s) ⊕ (get_z_flag m t s))).

(* if nIRQ=1, branch NB: irqflag e' un negato del pin *)
definition execute_BIH ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (get_irq_flag m t s)
  (λIRQ_op.execute_any_BRANCH m t s i cur_pc (⊖IRQ_op)).

(* if nIRQ=0, branch NB: irqflag e' un negato del pin *)
definition execute_BIL ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (get_irq_flag m t s)
  (λIRQ_op.execute_any_BRANCH m t s i cur_pc IRQ_op).

(* flags = A & M *)
definition execute_BIT ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_AND_BIT_EOR_ORA_aux m t s i cur_pc false and_b8.

(* if Z|N⊙V=1, branch *)
definition execute_BLE ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (get_n_flag m t s)
  (λN_op.opt_map ?? (get_v_flag m t s)
   (λV_op.execute_any_BRANCH m t s i cur_pc ((get_z_flag m t s) ⊕ (N_op ⊙ V_op)))).

(* if C|Z=1, branch *)
definition execute_BLS ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_any_BRANCH m t s i cur_pc ((get_c_flag m t s) ⊕ (get_z_flag m t s)).

(* if N⊙V=1, branch *)
definition execute_BLT ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (get_n_flag m t s)
  (λN_op.opt_map ?? (get_v_flag m t s)
   (λV_op.execute_any_BRANCH m t s i cur_pc (N_op ⊙ V_op))).

(* if I=0, branch *)
definition execute_BMC ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (get_i_flag m t s)
  (λI_op.execute_any_BRANCH m t s i cur_pc (⊖I_op)).

(* if N=1, branch *)
definition execute_BMI ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (get_n_flag m t s)
  (λN_op.execute_any_BRANCH m t s i cur_pc N_op).

(* if I=1, branch *)
definition execute_BMS ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (get_i_flag m t s)
  (λI_op.execute_any_BRANCH m t s i cur_pc I_op).

(* if Z=0, branch *)
definition execute_BNE ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_any_BRANCH m t s i cur_pc (⊖(get_z_flag m t s)).

(* if N=0, branch *)
definition execute_BPL ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (get_n_flag m t s)
  (λN_op.execute_any_BRANCH m t s i cur_pc (⊖N_op)).

(* branch always *)
definition execute_BRA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_any_BRANCH m t s i cur_pc true.

(* if Mn=0 branch *)
definition execute_BRCLRn ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_BRCLRn_BRSETn_aux m t s i cur_pc
  (λMn_op.eq_b8 Mn_op 〈x0,x0〉).

(* branch never... come se fosse un nop da 2 byte *)
definition execute_BRN ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_any_BRANCH m t s i cur_pc false.

(* if Mn=1 branch *)
definition execute_BRSETn ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_BRCLRn_BRSETn_aux m t s i cur_pc
  (λMn_op.⊖(eq_b8 Mn_op 〈x0,x0〉)).

(* Mn = 1 *)
definition execute_BSETn ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_BCLRn_BSETn_aux m t s i cur_pc 〈xF,xF〉.

(* branch to subroutine *)
(* HC05/HC08/HCS08 si appoggiano allo stack, RS08 a SPC *)
definition execute_BSR ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t .λi:instr_mode.λcur_pc:word16.
 opt_map ?? (multi_mode_load true m t s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ tripleT s_tmp1 M_op new_pc ⇒ let aux ≝
    (* push (new_pc low) *)
    opt_map ?? (aux_push m t s_tmp1 (w16l new_pc))
     (* push (new_pc high) *)
     (λs_tmp2.opt_map ?? (aux_push m t s_tmp2 (w16h new_pc))
      (* new_pc = new_pc + rel *)
      (λs_tmp3.Some ? (pair ?? s_tmp3 (branched_pc m t s_tmp3 new_pc M_op))))
     in match m with
    [ HC05 ⇒ aux | HC08 ⇒ aux | HCS08 ⇒ aux
    | RS08 ⇒
     (* SPC = new_pc *) 
     opt_map ?? (set_spc_reg m t s_tmp1 new_pc)
      (* new_pc = new_pc + rel *)
      (λs_tmp2.Some ? (pair ?? s_tmp2 (branched_pc m t s_tmp2 new_pc M_op)))
    ]]).

(* if A=M, branch *)
definition execute_CBEQA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (multi_mode_load false m t s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ tripleT s_tmp1 M_op new_pc ⇒
    match M_op with
     [ mk_word16 MH_op ML_op ⇒
      (* if A=M, branch *)
      match eq_b8 (get_acc_8_low_reg m t s_tmp1) MH_op with
       (* new_pc = new_pc + rel *)
       [ true ⇒ Some ? (pair ?? s_tmp1 (branched_pc m t s_tmp1 new_pc ML_op))
       (* new_pc = new_pc *)
       | false ⇒ Some ? (pair ?? s_tmp1 new_pc)
       ]]]).

(* if X=M, branch *)
definition execute_CBEQX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (multi_mode_load false m t s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ tripleT s_tmp1 M_op new_pc ⇒
    match M_op with
     [ mk_word16 MH_op ML_op ⇒
      opt_map ?? (get_indX_8_low_reg m t s_tmp1)
       (* if X=M, branch *)
       (λX_op.match eq_b8 X_op MH_op with
        (* new_pc = new_pc + rel *)
        [ true ⇒ Some ? (pair ?? s_tmp1 (branched_pc m t s_tmp1 new_pc ML_op))
        (* new_pc = new_pc *)
        | false ⇒ Some ? (pair ?? s_tmp1 new_pc)
        ])]]).

(* C = 0 *)
definition execute_CLC ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 Some ? (pair ?? (set_c_flag m t s false) cur_pc).

(* I = 0 *)
definition execute_CLI ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (set_i_flag m t s false)
  (λs_tmp.Some ? (pair ?? s_tmp cur_pc)).

(* M = 0 *)
definition execute_CLR ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 (* M = 0 *)
 opt_map ?? (multi_mode_write true m t s cur_pc i 〈x0,x0〉)
  (λS_PC.match S_PC with
   [ pair s_tmp1 new_pc ⇒
   (* Z = 1 *)
   let s_tmp2 ≝ set_z_flag m t s_tmp1 true in
   (* N = 0 *)
   let s_tmp3 ≝ setweak_n_flag m t s_tmp2 false in
   (* V = 0 *)
   let s_tmp4 ≝ setweak_v_flag m t s_tmp3 false in
   (* newpc = nextpc *)
   Some ? (pair ?? s_tmp4 new_pc) ]).

(* flags = A - M *)
definition execute_CMP ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_SBC_SUB_aux m t s i cur_pc false (λA_op.λM_op.λC_op.plus_b8 A_op (compl_b8 M_op) false). 

(* M = not M *)
definition execute_COM ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_COM_DEC_INC_NEG_aux m t s i cur_pc not_b8
 (* fV = 0 *)
 (λM7.λR7.false)
 (* fC = 1 *)
 (λC_op.λR_op.true).

(* flags = H:X - M *)
definition execute_CPHX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (multi_mode_load false m t s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ tripleT s_tmp1 M_op new_pc ⇒
    opt_map ?? (get_indX_16_reg m t s_tmp1)
     (λX_op. 
      match plus_w16 X_op (compl_w16 M_op) false with
       [ pair R_op carry ⇒
        let X15 ≝ MSB_w16 X_op in let M15 ≝ MSB_w16 M_op in let R15 ≝ MSB_w16 R_op in
        (* Z = nR15&nR14&nR13&nR12&nR11&nR10&nR9&nR8&nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
        let s_tmp2 ≝ set_z_flag m t s_tmp1 (eq_w16 R_op 〈〈x0,x0〉:〈x0,x0〉〉) in
        (* C = nX15&M15 | M15&R15 | R15&nX15 *)
        let s_tmp3 ≝ set_c_flag m t s_tmp2 (((⊖X15)⊗M15) ⊕ (M15⊗R15) ⊕ (R15⊗(⊖X15))) in
        (* N = R15 *) 
        let s_tmp4 ≝ setweak_n_flag m t s_tmp3 R15 in
        (* V = X15&nM15&nR15 | nX15&M15&R15 *)
        let s_tmp5 ≝ setweak_v_flag m t s_tmp4 ((X15⊗(⊖M15)⊗(⊖R15)) ⊕ ((⊖X15)⊗M15⊗R15)) in
        (* newpc = nextpc *)
        Some ? (pair ?? s_tmp5 new_pc) ] ) ]).

(* flags = X - M *)
definition execute_CPX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (multi_mode_load true m t s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ tripleT s_tmp1 M_op new_pc ⇒
    opt_map ?? (get_indX_8_low_reg m t s_tmp1)
     (λX_op. 
      match plus_b8 X_op (compl_b8 M_op) false with
       [ pair R_op carry ⇒
        let X7 ≝ MSB_b8 X_op in let M7 ≝ MSB_b8 M_op in let R7 ≝ MSB_b8 R_op in
        (* Z = nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
        let s_tmp2 ≝ set_z_flag m t s_tmp1 (eq_b8 R_op 〈x0,x0〉) in
        (* C = nX7&M7 | M7&R7 | R7&nX7 *)
        let s_tmp3 ≝ set_c_flag m t s_tmp2 (((⊖X7)⊗M7) ⊕ (M7⊗R7) ⊕ (R7⊗(⊖X7))) in
        (* N = R7 *) 
        let s_tmp4 ≝ setweak_n_flag m t s_tmp3 R7 in
        (* V = X7&nM7&nR7 | nX7&M7&R7 *)
        let s_tmp5 ≝ setweak_v_flag m t s_tmp4 ((X7⊗(⊖M7)⊗(⊖R7)) ⊕ ((⊖X7)⊗M7⊗R7)) in
        (* newpc = nextpc *)
        Some ? (pair ?? s_tmp5 new_pc) ] ) ]).

(* decimal adjiust A *)
(* per i dettagli vedere daa_b8 (modulo byte8) *)
definition execute_DAA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (get_h_flag m t s)
  (λH.
   let M_op ≝ get_acc_8_low_reg m t s in
   match daa_b8 H (get_c_flag m t s) M_op with
    [ pair R_op carry ⇒
     (* A = R *)
     let s_tmp1 ≝ set_acc_8_low_reg m t s R_op in
     (* Z = nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
     let s_tmp2 ≝ set_z_flag m t s_tmp1 (eq_b8 R_op 〈x0,x0〉) in
     (* C = carry *)
     let s_tmp3 ≝ set_c_flag m t s_tmp2 carry in
     (* N = R7 *) 
     let s_tmp4 ≝ setweak_n_flag m t s_tmp3 (MSB_b8 R_op) in
     (* V = M7 ⊙ R7 *)
     let s_tmp5 ≝ setweak_v_flag m t s_tmp4 ((MSB_b8 M_op) ⊙ (MSB_b8 R_op)) in
     (* newpc = curpc *)
     Some ? (pair ?? s_tmp5 cur_pc) ]).

(* if (--M)≠0, branch *)
definition execute_DBNZ ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (multi_mode_load false m t s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ tripleT s_tmp1 M_op new_pc ⇒
    match M_op with
     [ mk_word16 MH_op ML_op ⇒
     (* --M *)
     let MH_op' ≝ pred_b8 MH_op in
     opt_map ?? (multi_mode_write true m t s_tmp1 cur_pc i MH_op')
      (λS_PC.match S_PC with
       [ pair s_tmp2 _ ⇒
        (* if (--M)≠0, branch *)
        match eq_b8 MH_op' 〈x0,x0〉 with
         (* new_pc = new_pc *)
         [ true ⇒ Some ? (pair ?? s_tmp2 new_pc)
         (* new_pc = new_pc + rel *)
         | false ⇒ Some ? (pair ?? s_tmp2 (branched_pc m t s_tmp2 new_pc ML_op)) ]])]]).

(* M = M - 1 *)
definition execute_DEC ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_COM_DEC_INC_NEG_aux m t s i cur_pc pred_b8
 (* fV = M7&nR7 *)
 (λM7.λR7.M7⊗(⊖R7))
 (* fC = C *)
 (λC_op.λR_op.C_op).

(* A = H:A/X, H = H:AmodX se non c'e' overflow, altrimenti invariati *)
(* per i dettagli vedere div_b8 (modulo word16) *)
definition execute_DIV ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (get_indX_8_high_reg m t s)
  (λH_op.opt_map ?? (get_indX_8_low_reg m t s)
   (λX_op.match div_b8 〈H_op:(get_acc_8_low_reg m t s)〉 X_op with
    [ tripleT quoz rest overflow ⇒
     (* C = overflow *)
     let s_tmp1 ≝ set_c_flag m t s overflow in
     (* A = A o H:A/X *)
     let s_tmp2 ≝ match overflow with
      [ true ⇒ s_tmp1
      | false ⇒ set_acc_8_low_reg m t s_tmp1 quoz ] in
     (* Z = nA7&nA6&nA5&nA4&nA3&nA2&nA1&nA0 *)
     (* NB: che A sia cambiato o no, lo testa *)
     let s_tmp3 ≝ set_z_flag m t s_tmp2 (eq_b8 (get_acc_8_low_reg m t s_tmp2) 〈x0,x0〉) in
     (* H = H o H:AmodX *)
     opt_map ?? (match overflow with
                 [ true ⇒ Some ? s_tmp3
                 | false ⇒ set_indX_8_high_reg m t s_tmp3 rest])
      (λs_tmp4.Some ? (pair ?? s_tmp4 cur_pc)) ])).

(* A = A ⊙ M *)
definition execute_EOR ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_AND_BIT_EOR_ORA_aux m t s i cur_pc true xor_b8.

(* M = M + 1 *)
definition execute_INC ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_COM_DEC_INC_NEG_aux m t s i cur_pc succ_b8
 (* fV = nM7&R7 *)
 (λM7.λR7.(⊖M7)⊗R7)
 (* fC = C *)
 (λC_op.λR_op.C_op).

(* jmp, il nuovo indirizzo e' una WORD *)
definition execute_JMP ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (multi_mode_load false m t s cur_pc i)
  (λS_M_PC.
   (* newpc = M_op *)
   Some ? (pair ?? (fst3T ??? S_M_PC) (snd3T ??? S_M_PC))).

(* jump to subroutine *)
(* HC05/HC08/HCS08 si appoggiano allo stack, RS08 a SPC *)
definition execute_JSR ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (multi_mode_load false m t s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ tripleT s_tmp1 M_op new_pc ⇒ let aux ≝
    (* push (new_pc low) *)
    opt_map ?? (aux_push m t s_tmp1 (w16l new_pc))
     (* push (new_pc high) *)
     (λs_tmp2.opt_map ?? (aux_push m t s_tmp2 (w16h new_pc))
      (* newpc = M_op *)
      (λs_tmp3.Some ? (pair ?? s_tmp3 M_op)))
     in match m with
    [ HC05 ⇒ aux | HC08 ⇒ aux | HCS08 ⇒ aux
    | RS08 ⇒
     (* SPC = new_pc *) 
     opt_map ?? (set_spc_reg m t s_tmp1 new_pc)
      (* newpc = M_op *)
      (λs_tmp2.Some ? (pair ?? s_tmp2 M_op))
    ]]).

(* A = M *)
definition execute_LDA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (multi_mode_load true m t s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ tripleT s_tmp1 M_op new_pc ⇒
    (* A = M *) 
    let s_tmp2 ≝ set_acc_8_low_reg m t s_tmp1 M_op in
    (* Z = nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
    let s_tmp3 ≝ set_z_flag m t s_tmp2 (eq_b8 M_op 〈x0,x0〉) in
    (* N = R7 *) 
    let s_tmp4 ≝ setweak_n_flag m t s_tmp3 (MSB_b8 M_op) in
    (* V = 0 *) 
    let s_tmp5 ≝ setweak_v_flag m t s_tmp4 false in
    (* newpc = nextpc *)
    Some ? (pair ?? s_tmp5 new_pc) ]).

(* H:X = M *)
definition execute_LDHX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (multi_mode_load false m t s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ tripleT s_tmp1 M_op new_pc ⇒
    opt_map ?? (set_indX_16_reg m t s_tmp1 M_op)
     (λs_tmp2.
      (* Z = nR15&nR14&nR13nR12&nR11&nR10&nR9&nR8nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
      let s_tmp3 ≝ set_z_flag m t s_tmp2 (eq_w16 M_op 〈〈x0,x0〉:〈x0,x0〉〉) in
      (* N = R15 *)
      let s_tmp4 ≝ setweak_n_flag m t s_tmp3 (MSB_w16 M_op) in
      (* V = 0 *) 
      let s_tmp5 ≝ setweak_v_flag m t s_tmp4 false in
      (* newpc = nextpc *)
      Some ? (pair ?? s_tmp5 new_pc)) ]).

(* X = M *)
definition execute_LDX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (multi_mode_load true m t s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ tripleT s_tmp1 M_op new_pc ⇒
    opt_map ?? (set_indX_8_low_reg m t s_tmp1 M_op)
     (λs_tmp2.
      (* Z = nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
      let s_tmp3 ≝ set_z_flag m t s_tmp2 (eq_b8 M_op 〈x0,x0〉) in
      (* N = R7 *)
      let s_tmp4 ≝ setweak_n_flag m t s_tmp3 (MSB_b8 M_op) in
      (* V = 0 *) 
      let s_tmp5 ≝ setweak_v_flag m t s_tmp4 false in
      (* newpc = nextpc *)
      Some ? (pair ?? s_tmp5 new_pc)) ]).

(* M = 0 -> rcr M -> C' *)
definition execute_LSR ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_ASL_ASR_LSR_ROL_ROR_aux m t s i cur_pc (λM_op.λC_op.rcr_b8 M_op false).

(* M2 = M1 *)
definition execute_MOV ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 (* R_op = M1 *)
 opt_map ?? (multi_mode_load true m t s cur_pc i)
  (λS_R_PC.match S_R_PC with
   [ tripleT s_tmp1 R_op tmp_pc ⇒
    (* M2 = R_op *)
    opt_map ?? (multi_mode_write true m t s_tmp1 tmp_pc i R_op)
     (λS_PC.match S_PC with
      [ pair s_tmp2 new_pc ⇒
       (* Z = nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
       let s_tmp3 ≝ set_z_flag m t s_tmp2 (eq_b8 R_op 〈x0,x0〉) in
       (* N = R7 *)
       let s_tmp4 ≝ setweak_n_flag m t s_tmp3 (MSB_b8 R_op) in
       (* V = 0 *) 
       let s_tmp5 ≝ setweak_v_flag m t s_tmp4 false in
       (* newpc = nextpc *)
       Some ? (pair ?? s_tmp5 new_pc)])]).

(* X:A = X * A *)
definition execute_MUL ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (get_indX_8_low_reg m t s)
  (λX_op.let R_op ≝ mul_b8 X_op (get_acc_8_low_reg m t s) in
   opt_map ?? (set_indX_8_low_reg m t s (w16h R_op))
    (λs_tmp.Some ? (pair ?? (set_acc_8_low_reg m t s_tmp (w16l R_op)) cur_pc))).

(* M = compl M *)
definition execute_NEG ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_COM_DEC_INC_NEG_aux m t s i cur_pc compl_b8
 (* fV = M7&R7 *)
 (λM7.λR7.M7⊗R7)
 (* fC = R7|R6|R5|R4|R3|R2|R1|R0 *)
 (λC_op.λR_op.⊖(eq_b8 R_op 〈x0,x0〉)).

(* nulla *)
definition execute_NOP ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 Some ? (pair ?? s cur_pc).

(* A = (mk_byte8 (b8l A) (b8h A)) *)
(* cioe' swap del nibble alto/nibble basso di A *)
definition execute_NSA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 match get_acc_8_low_reg m t s with [ mk_byte8 ah al ⇒
  (* A = (mk_byte8 (b8l A) (b8h A)) *)
  Some ? (pair ?? (set_acc_8_low_reg m t s 〈al,ah〉) cur_pc) ].

(* A = A | M *)
definition execute_ORA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_AND_BIT_EOR_ORA_aux m t s i cur_pc true or_b8.

(* push A *)
definition execute_PSHA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (aux_push m t s (get_acc_8_low_reg m t s))
  (λs_tmp1.Some ? (pair ?? s_tmp1 cur_pc)).

(* push H *)
definition execute_PSHH ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (get_indX_8_high_reg m t s)
  (λH_op.opt_map ?? (aux_push m t s H_op)
   (λs_tmp1.Some ? (pair ?? s_tmp1 cur_pc))).

(* push X *)
definition execute_PSHX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (get_indX_8_low_reg m t s)
  (λH_op.opt_map ?? (aux_push m t s H_op)
   (λs_tmp1.Some ? (pair ?? s_tmp1 cur_pc))).

(* pop A *)
definition execute_PULA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (aux_pop m t s)
  (λS_and_A.match S_and_A with [ pair s_tmp1 A_op ⇒
   Some ? (pair ?? (set_acc_8_low_reg m t s_tmp1 A_op) cur_pc) ]).

(* pop H *)
definition execute_PULH ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (aux_pop m t s)
  (λS_and_H.match S_and_H with [ pair s_tmp1 H_op ⇒
   opt_map ?? (set_indX_8_high_reg m t s_tmp1 H_op)
    (λs_tmp2.Some ? (pair ?? s_tmp2 cur_pc))]).

(* pop X *)
definition execute_PULX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (aux_pop m t s)
  (λS_and_X.match S_and_X with [ pair s_tmp1 X_op ⇒
   opt_map ?? (set_indX_8_low_reg m t s_tmp1 X_op)
    (λs_tmp2.Some ? (pair ?? s_tmp2 cur_pc))]).

(* M = C' <- rcl M <- C *)
definition execute_ROL ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_ASL_ASR_LSR_ROL_ROR_aux m t s i cur_pc (λM_op.λC_op.rcl_b8 M_op C_op).

(* M = C -> rcr M -> C' *)
definition execute_ROR ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_ASL_ASR_LSR_ROL_ROR_aux m t s i cur_pc (λM_op.λC_op.rcr_b8 M_op C_op).

(* SP = 0xuuFF *)
(* lascia inalterato il byte superiore di SP *)
definition execute_RSP ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (get_sp_reg m t s)
  (λSP_op.match SP_op with [ mk_word16 sph spl ⇒
   opt_map ?? (set_sp_reg m t s 〈sph:〈xF,xF〉〉)
    (λs_tmp.Some ? (pair ?? s_tmp cur_pc))]).

(* return from interrupt *)
definition execute_RTI ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 (* pop (CCR) *)
 opt_map ?? (aux_pop m t s)
  (λS_and_CCR.match S_and_CCR with [ pair s_tmp1 CCR_op ⇒
   let s_tmp2 ≝ aux_set_CCR m t s_tmp1 CCR_op in
   (* pop (A) *)
   opt_map ?? (aux_pop m t s_tmp2)
    (λS_and_A.match S_and_A with [ pair s_tmp3 A_op ⇒
     let s_tmp4 ≝ set_acc_8_low_reg m t s_tmp3 A_op in
     (* pop (X) *)
     opt_map ?? (aux_pop m t s_tmp4)
      (λS_and_X.match S_and_X with [ pair s_tmp5 X_op ⇒
       opt_map ?? (set_indX_8_low_reg m t s_tmp5 X_op)
        (* pop (PC high) *)
        (λs_tmp6.opt_map ?? (aux_pop m t s_tmp6)
         (λS_and_PCH.match S_and_PCH with [ pair s_tmp7 PCH_op ⇒
          (* pop (PC low) *)
          opt_map ?? (aux_pop m t s_tmp7)
           (λS_and_PCL.match S_and_PCL with [ pair s_tmp8 PCL_op ⇒
            Some ? (pair ?? s_tmp8 〈PCH_op:PCL_op〉)])]))])])]).

(* return from subroutine *)
(* HC05/HC08/HCS08 si appoggia allo stack, RS08 si appoggia a SPC *)
definition execute_RTS ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 let aux ≝
  (* pop (PC high) *)
  opt_map ?? (aux_pop m t s)
   (λS_and_PCH.match S_and_PCH with [ pair s_tmp1 PCH_op ⇒
    (* pop (PC low) *)
    opt_map ?? (aux_pop m t s_tmp1)
     (λS_and_PCL.match S_and_PCL with [ pair s_tmp2 PCL_op ⇒
      Some ? (pair ?? s_tmp2 〈PCH_op:PCL_op〉)])])
 in match m with
  [ HC05 ⇒ aux | HC08 ⇒ aux | HCS08 ⇒ aux
  | RS08 ⇒
   (* new_pc = SPC *)
   opt_map ?? (get_spc_reg m t s)
    (λSPC_op.Some ? (pair ?? s SPC_op))
  ].

(* A = A - M - C *)
definition execute_SBC ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_SBC_SUB_aux m t s i cur_pc true
 (λA_op.λM_op.λC_op.match plus_b8 A_op (compl_b8 M_op) false with
  [ pair resb resc ⇒ match C_op with
   [ true ⇒ plus_b8 resb 〈xF,xF〉 false
   | false ⇒ pair ?? resb resc ]]).

(* C = 1 *)
definition execute_SEC ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 Some ? (pair ?? (set_c_flag m t s true) cur_pc).

(* I = 1 *)
definition execute_SEI ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (set_i_flag m t s true)
  (λs_tmp.Some ? (pair ?? s_tmp cur_pc)).

(* swap SPCh,A *)
(* senso: nell'RS08 SPC non e' accessibile direttamente e come si possono
          fare subroutine annidate se RA (return address) e' salvato sempre in SPC?
          occore accedere a SPC e salvarne il contenuto *)
definition execute_SHA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (get_spc_reg m t s)
  (λSPC_op.opt_map ?? (set_spc_reg m t s 〈(get_acc_8_low_reg m t s):(w16l SPC_op)〉)
   (λs_tmp1.Some ? (pair ?? (set_acc_8_low_reg m t s_tmp1 (w16h SPC_op)) cur_pc))).

(* swap SPCl,A *)
(* senso: nell'RS08 SPC non e' accessibile direttamente e come si possono
          fare subroutine annidate se RA (return address) e' salvato sempre in SPC?
          occore accedere a SPC e salvarne il contenuto *)
definition execute_SLA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (get_spc_reg m t s)
  (λSPC_op.opt_map ?? (set_spc_reg m t s 〈(w16h SPC_op):(get_acc_8_low_reg m t s)〉)
   (λs_tmp1.Some ? (pair ?? (set_acc_8_low_reg m t s_tmp1 (w16l SPC_op)) cur_pc))).

(* M = A *)
definition execute_STA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 (* M = A *)
 let A_op ≝ (get_acc_8_low_reg m t s) in
 opt_map ?? (multi_mode_write true m t s cur_pc i A_op)
  (λS_op_and_PC.match S_op_and_PC with
   [ pair s_tmp1 new_pc ⇒
   (* Z = nA7&nA6&nA5&nA4&nA3&nA2&nA1&nA0 *)
   let s_tmp2 ≝ set_z_flag m t s_tmp1 (eq_b8 A_op 〈x0,x0〉) in
   (* N = A7 *)
   let s_tmp3 ≝ setweak_n_flag m t s_tmp2 (MSB_b8 A_op) in
   (* V = 0 *)
   let s_tmp4 ≝ setweak_v_flag m t s_tmp3 false in
   (* newpc = nextpc *)
   Some ? (pair ?? s_tmp4 new_pc) ]).

(* M = H:X *)
definition execute_STHX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 (* M = H:X *)
 opt_map ?? (get_indX_16_reg m t s)
  (λX_op.opt_map ?? (multi_mode_write false m t s cur_pc i X_op)
   (λS_op_and_PC.match S_op_and_PC with
    [ pair s_tmp1 new_pc ⇒
     (* Z = nR15&nR14&nR13nR12&nR11&nR10&nR9&nR8nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
     let s_tmp2 ≝ set_z_flag m t s_tmp1 (eq_w16 X_op 〈〈x0,x0〉:〈x0,x0〉〉) in
     (* N = R15 *)
     let s_tmp3 ≝ setweak_n_flag m t s_tmp2 (MSB_w16 X_op) in
     (* V = 0 *)
     let s_tmp4 ≝ setweak_v_flag m t s_tmp3 false in
     (* newpc = nextpc *)
      Some ? (pair ?? s_tmp4 new_pc) ])).

(* I = 0 *)
definition execute_STOP ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 Some ? (pair ?? (setweak_i_flag m t s false) cur_pc).

(* M = X *)
definition execute_STX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 (* M = X *)
 opt_map ?? (get_indX_8_low_reg m t s)
  (λX_op.opt_map ?? (multi_mode_write true m t s cur_pc i X_op)
   (λS_op_and_PC.match S_op_and_PC with
    [ pair s_tmp1 new_pc ⇒
     (* Z = nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
     let s_tmp2 ≝ set_z_flag m t s_tmp1 (eq_b8 X_op 〈x0,x0〉) in
     (* N = R7 *)
     let s_tmp3 ≝ setweak_n_flag m t s_tmp2 (MSB_b8 X_op) in
     (* V = 0 *)
     let s_tmp4 ≝ setweak_v_flag m t s_tmp3 false in
     (* newpc = nextpc *)
     Some ? (pair ?? s_tmp4 new_pc) ])).

(* A = A - M *)
definition execute_SUB ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 execute_SBC_SUB_aux m t s i cur_pc true (λA_op.λM_op.λC_op.plus_b8 A_op (compl_b8 M_op) false). 

(* software interrupt *)
definition execute_SWI ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 (* indirizzo da cui caricare il nuovo pc *)
 let vector ≝ get_pc_reg m t (set_pc_reg m t s 〈〈xF,xF〉:〈xF,xC〉〉) in
 (* push (cur_pc low) *)
 opt_map ?? (aux_push m t s (w16l cur_pc))
  (* push (cur_pc high *)
  (λs_tmp1.opt_map ?? (aux_push m t s_tmp1 (w16h cur_pc))
   (λs_tmp2.opt_map ?? (get_indX_8_low_reg m t s_tmp2)
    (* push (X) *)
    (λX_op.opt_map ?? (aux_push m t s_tmp2 X_op)
     (* push (A) *)
     (λs_tmp3.opt_map ?? (aux_push m t s_tmp3 (get_acc_8_low_reg m t s_tmp3))
      (* push (CCR) *)
      (λs_tmp4.opt_map ?? (aux_push m t s_tmp4 (aux_get_CCR m t s_tmp4))
       (* I = 1 *)
       (λs_tmp5.opt_map ?? (set_i_flag m t s_tmp5 true)
        (* load from vector high *)
        (λs_tmp6.opt_map ?? (memory_filter_read m t s_tmp6 vector)
         (* load from vector low *)
         (λaddrh.opt_map ?? (memory_filter_read m t s_tmp6 (succ_w16 vector))
          (* newpc = [vector] *)
          (λaddrl.Some ? (pair ?? s_tmp6 〈addrh:addrl〉)))))))))).

(* flags = A *)
definition execute_TAP ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 Some ? (pair ?? (aux_set_CCR m t s (get_acc_8_low_reg m t s)) cur_pc). 

(* X = A *)
definition execute_TAX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (set_indX_8_low_reg m t s (get_acc_8_low_reg m t s))
  (λs_tmp.Some ? (pair ?? s_tmp cur_pc)).

(* A = flags *)
definition execute_TPA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 Some ? (pair ?? (set_acc_8_low_reg m t s (aux_get_CCR m t s)) cur_pc).

(* flags = M - 0 *)
(* implementata senza richiamare la sottrazione, la modifica dei flag
   e' immediata *)
definition execute_TST ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (multi_mode_load true m t s cur_pc i)
  (λS_M_PC.match S_M_PC with
   [ tripleT s_tmp1 M_op new_pc ⇒
    (* Z = nR7&nR6&nR5&nR4&nR3&nR2&nR1&nR0 *)
    let s_tmp2 ≝ set_z_flag m t s_tmp1 (eq_b8 M_op 〈x0,x0〉) in
    (* N = R7 *) 
    let s_tmp3 ≝ setweak_n_flag m t s_tmp2 (MSB_b8 M_op) in
    (* V = 0 *) 
    let s_tmp4 ≝ setweak_v_flag m t s_tmp3 false in
    (* newpc = nextpc *)
    Some ? (pair ?? s_tmp4 new_pc) ]).

(* H:X = SP + 1 *)
definition execute_TSX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (get_sp_reg m t s )
  (λSP_op.opt_map ?? (set_indX_16_reg m t s (succ_w16 SP_op))
   (* H:X = SP + 1 *)
   (λs_tmp.Some ? (pair ?? s_tmp cur_pc))).

(* A = X *)
definition execute_TXA ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (get_indX_8_low_reg m t s)
  (λX_op.Some ? (pair ?? (set_acc_8_low_reg m t s X_op) cur_pc)).

(* SP = H:X - 1 *)
definition execute_TXS ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 opt_map ?? (get_indX_16_reg m t s )
  (λX_op.opt_map ?? (set_sp_reg m t s (pred_w16 X_op))
   (* SP = H:X - 1 *)
   (λs_tmp.Some ? (pair ?? s_tmp cur_pc))).

(* I = 0 *)
definition execute_WAIT ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λi:instr_mode.λcur_pc:word16.
 Some ? (pair ?? (setweak_i_flag m t s false) cur_pc).

(* **** *)
(* TICK *)
(* **** *)

(* enumerazione delle possibili modalita' di sospensione *)
inductive susp_type : Type ≝
  BGND_MODE: susp_type
| STOP_MODE: susp_type
| WAIT_MODE: susp_type.

(* un tipo opzione ad hoc
   - errore: errore+stato (seguira' reset o ??, cmq lo stato non va buttato)
   - sospensione: sospensione+stato (seguira' resume o ??)
   - ok: stato
*)
inductive tick_result (A:Type) : Type ≝
  TickERR   : A → error_type → tick_result A
| TickSUSP  : A → susp_type → tick_result A
| TickOK    : A → tick_result A.

(* sostanazialmente simula
   - fetch/decode/execute
   - l'esecuzione e' considerata atomica quindi nel caso di un'instruzione
     da 3 cicli la successione sara'
       ([fetch/decode] s,clk:None) →
       (               s,clk:Some 1,pseudo,mode,3,cur_pc) →
       (               s,clk:Some 2,pseudo,mode,3,cur_pc) →
       ([execute]      s',clk:None) *)

definition tick_execute ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
λpseudo:any_opcode m.λmode:instr_mode.λcur_pc:word16.
 let abs_pseudo ≝ match pseudo with [ anyOP pseudo' ⇒ pseudo' ] in
 let a_status_and_fetch ≝ match abs_pseudo with
  [ ADC    ⇒ execute_ADC    m t s mode cur_pc (* add with carry *)
  | ADD    ⇒ execute_ADD    m t s mode cur_pc (* add *)
  | AIS    ⇒ execute_AIS    m t s mode cur_pc (* add immediate to SP *)
  | AIX    ⇒ execute_AIX    m t s mode cur_pc (* add immediate to X *)
  | AND    ⇒ execute_AND    m t s mode cur_pc (* and *)
  | ASL    ⇒ execute_ASL    m t s mode cur_pc (* aritmetic shift left *)
  | ASR    ⇒ execute_ASR    m t s mode cur_pc (* aritmetic shift right *)
  | BCC    ⇒ execute_BCC    m t s mode cur_pc (* branch if C=0 *)
  | BCLRn  ⇒ execute_BCLRn  m t s mode cur_pc (* clear bit n *)
  | BCS    ⇒ execute_BCS    m t s mode cur_pc (* branch if C=1 *)
  | BEQ    ⇒ execute_BEQ    m t s mode cur_pc (* branch if Z=1 *)
  | BGE    ⇒ execute_BGE    m t s mode cur_pc (* branch if N⊙V=0 (great or equal) *)
  | BGND   ⇒ execute_BGND   m t s mode cur_pc (* !!background mode!!*)
  | BGT    ⇒ execute_BGT    m t s mode cur_pc (* branch if Z|N⊙V=0 clear (great) *)
  | BHCC   ⇒ execute_BHCC   m t s mode cur_pc (* branch if H=0 *)
  | BHCS   ⇒ execute_BHCS   m t s mode cur_pc (* branch if H=1 *)
  | BHI    ⇒ execute_BHI    m t s mode cur_pc (* branch if C|Z=0, (higher) *)
  | BIH    ⇒ execute_BIH    m t s mode cur_pc (* branch if nIRQ=1 *)
  | BIL    ⇒ execute_BIL    m t s mode cur_pc (* branch if nIRQ=0 *)
  | BIT    ⇒ execute_BIT    m t s mode cur_pc (* flag = and (bit test) *)
  | BLE    ⇒ execute_BLE    m t s mode cur_pc (* branch if Z|N⊙V=1 (less or equal) *)
  | BLS    ⇒ execute_BLS    m t s mode cur_pc (* branch if C|Z=1 (lower or same) *)
  | BLT    ⇒ execute_BLT    m t s mode cur_pc (* branch if N⊙1=1 (less) *)
  | BMC    ⇒ execute_BMC    m t s mode cur_pc (* branch if I=0 (interrupt mask clear) *)
  | BMI    ⇒ execute_BMI    m t s mode cur_pc (* branch if N=1 (minus) *)
  | BMS    ⇒ execute_BMS    m t s mode cur_pc (* branch if I=1 (interrupt mask set) *)
  | BNE    ⇒ execute_BNE    m t s mode cur_pc (* branch if Z=0 *)
  | BPL    ⇒ execute_BPL    m t s mode cur_pc (* branch if N=0 (plus) *)
  | BRA    ⇒ execute_BRA    m t s mode cur_pc (* branch always *)
  | BRCLRn ⇒ execute_BRCLRn m t s mode cur_pc (* branch if bit n clear *)
  | BRN    ⇒ execute_BRN    m t s mode cur_pc (* branch never (nop) *)
  | BRSETn ⇒ execute_BRSETn m t s mode cur_pc (* branch if bit n set *)
  | BSETn  ⇒ execute_BSETn  m t s mode cur_pc (* set bit n *)
  | BSR    ⇒ execute_BSR    m t s mode cur_pc (* branch to subroutine *)
  | CBEQA  ⇒ execute_CBEQA  m t s mode cur_pc (* compare (A) and BEQ *)
  | CBEQX  ⇒ execute_CBEQX  m t s mode cur_pc (* compare (X) and BEQ *)
  | CLC    ⇒ execute_CLC    m t s mode cur_pc (* C=0 *)
  | CLI    ⇒ execute_CLI    m t s mode cur_pc (* I=0 *)
  | CLR    ⇒ execute_CLR    m t s mode cur_pc (* operand=0 *)
  | CMP    ⇒ execute_CMP    m t s mode cur_pc (* flag = sub (compare A) *)
  | COM    ⇒ execute_COM    m t s mode cur_pc (* not (1 complement) *)
  | CPHX   ⇒ execute_CPHX   m t s mode cur_pc (* flag = sub (compare H:X) *)
  | CPX    ⇒ execute_CPX    m t s mode cur_pc (* flag = sub (compare X) *)
  | DAA    ⇒ execute_DAA    m t s mode cur_pc (* decimal adjust A *)
  | DBNZ   ⇒ execute_DBNZ   m t s mode cur_pc (* dec and BNE *)
  | DEC    ⇒ execute_DEC    m t s mode cur_pc (* operand=operand-1 (decrement) *)
  | DIV    ⇒ execute_DIV    m t s mode cur_pc (* div *)
  | EOR    ⇒ execute_EOR    m t s mode cur_pc (* xor *)
  | INC    ⇒ execute_INC    m t s mode cur_pc (* operand=operand+1 (increment) *)
  | JMP    ⇒ execute_JMP    m t s mode cur_pc (* jmp word [operand] *)
  | JSR    ⇒ execute_JSR    m t s mode cur_pc (* jmp to subroutine *)
  | LDA    ⇒ execute_LDA    m t s mode cur_pc (* load in A *)
  | LDHX   ⇒ execute_LDHX   m t s mode cur_pc (* load in H:X *)
  | LDX    ⇒ execute_LDX    m t s mode cur_pc (* load in X *)
  | LSR    ⇒ execute_LSR    m t s mode cur_pc (* logical shift right *)
  | MOV    ⇒ execute_MOV    m t s mode cur_pc (* move *)
  | MUL    ⇒ execute_MUL    m t s mode cur_pc (* mul *)
  | NEG    ⇒ execute_NEG    m t s mode cur_pc (* neg (2 complement) *)
  | NOP    ⇒ execute_NOP    m t s mode cur_pc (* nop *)
  | NSA    ⇒ execute_NSA    m t s mode cur_pc (* nibble swap A (al:ah <- ah:al) *)
  | ORA    ⇒ execute_ORA    m t s mode cur_pc (* or *)
  | PSHA   ⇒ execute_PSHA   m t s mode cur_pc (* push A *)
  | PSHH   ⇒ execute_PSHH   m t s mode cur_pc (* push H *)
  | PSHX   ⇒ execute_PSHX   m t s mode cur_pc (* push X *)
  | PULA   ⇒ execute_PULA   m t s mode cur_pc (* pop A *)
  | PULH   ⇒ execute_PULH   m t s mode cur_pc (* pop H *)
  | PULX   ⇒ execute_PULX   m t s mode cur_pc (* pop X *)
  | ROL    ⇒ execute_ROL    m t s mode cur_pc (* rotate left *)
  | ROR    ⇒ execute_ROR    m t s mode cur_pc (* rotate right *)
  | RSP    ⇒ execute_RSP    m t s mode cur_pc (* reset SP (0x00FF) *)
  | RTI    ⇒ execute_RTI    m t s mode cur_pc (* return from interrupt *)
  | RTS    ⇒ execute_RTS    m t s mode cur_pc (* return from subroutine *)
  | SBC    ⇒ execute_SBC    m t s mode cur_pc (* sub with carry*)
  | SEC    ⇒ execute_SEC    m t s mode cur_pc (* C=1 *)
  | SEI    ⇒ execute_SEI    m t s mode cur_pc (* I=1 *)
  | SHA    ⇒ execute_SHA    m t s mode cur_pc (* swap spc_high,A *)
  | SLA    ⇒ execute_SLA    m t s mode cur_pc (* swap spc_low,A *)
  | STA    ⇒ execute_STA    m t s mode cur_pc (* store from A *)
  | STHX   ⇒ execute_STHX   m t s mode cur_pc (* store from H:X *)
  | STOP   ⇒ execute_STOP   m t s mode cur_pc (* !!stop mode!! *)
  | STX    ⇒ execute_STX    m t s mode cur_pc (* store from X *)
  | SUB    ⇒ execute_SUB    m t s mode cur_pc (* sub *)
  | SWI    ⇒ execute_SWI    m t s mode cur_pc (* software interrupt *)
  | TAP    ⇒ execute_TAP    m t s mode cur_pc (* flag=A (transfer A to process status byte *)
  | TAX    ⇒ execute_TAX    m t s mode cur_pc (* X=A (transfer A to X) *)
  | TPA    ⇒ execute_TPA    m t s mode cur_pc (* A=flag (transfer process status byte to A) *)
  | TST    ⇒ execute_TST    m t s mode cur_pc (* flag = sub (test) *)
  | TSX    ⇒ execute_TSX    m t s mode cur_pc (* X:H=SP (transfer SP to H:X) *)
  | TXA    ⇒ execute_TXA    m t s mode cur_pc (* A=X (transfer X to A) *)
  | TXS    ⇒ execute_TXS    m t s mode cur_pc (* SP=X:H (transfer H:X to SP) *)
  | WAIT   ⇒ execute_WAIT   m t s mode cur_pc (* !!wait mode!!*)
  ] in match a_status_and_fetch with
(* errore nell'execute (=caricamento argomenti)? riportato in output *)
(* nessun avanzamento e clk a None *)
   [ None ⇒ TickERR ? (set_clk_desc m t s (None ?)) ILL_EX_AD
   | Some status_and_newpc ⇒
(* aggiornamento centralizzato di pc e clk *)
     match status_and_newpc with
      [ pair s_tmp1 new_pc ⇒
       let s_tmp2 ≝ set_pc_reg m t s_tmp1 new_pc in
       let s_tmp3 ≝ set_clk_desc m t s_tmp2 (None ?) in
       let abs_magic ≝ magic_of_opcode abs_pseudo in
(* distinzione fra le 4 modalita' possibili, normale/BGND/STOP/WAIT *)
        match eq_b8 abs_magic (magic_of_opcode BGND) with
         [ true ⇒ TickSUSP ? s_tmp3 BGND_MODE
         | false ⇒ match eq_b8 abs_magic (magic_of_opcode STOP) with
          [ true ⇒ TickSUSP ? s_tmp3 STOP_MODE
          | false ⇒ match eq_b8 abs_magic (magic_of_opcode WAIT) with
           [ true ⇒ TickSUSP ? s_tmp3 WAIT_MODE
           | false ⇒ TickOK ? s_tmp3
           ]]]]].

definition tick ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 let opt_info ≝ get_clk_desc m t s in
 match opt_info with
  (* e' il momento del fetch *)
  [ None ⇒ match fetch m t s with
   (* errore nel fetch/decode? riportato in output, nessun avanzamento *)
   [ FetchERR err ⇒ TickERR ? s err
   (* nessun errore nel fetch *)
   | FetchOK fetch_info cur_pc ⇒ match fetch_info with
    [ quadrupleT pseudo mode _ tot_clk ⇒
      match eq_b8 〈x0,x1〉 tot_clk with
       (* un solo clk, execute subito *)
       [ true ⇒ tick_execute m t s pseudo mode cur_pc
       (* piu' clk, execute rimandata *)
       | false ⇒ TickOK ? (set_clk_desc m t s (Some ? (quintupleT ????? 〈x0,x1〉 pseudo mode tot_clk cur_pc)))
       ]
      ]
    ]
  (* il fetch e' gia' stato eseguito, e' il turno di execute? *)
  | Some info ⇒ match info with [ quintupleT cur_clk pseudo mode tot_clk cur_pc ⇒ 
   match eq_b8 (succ_b8 cur_clk) tot_clk with
    (* si *)
    [ true ⇒ tick_execute m t s pseudo mode cur_pc
    (* no, avanzamento cur_clk *)
    | false ⇒ TickOK ? (set_clk_desc m t s (Some ? (quintupleT ????? (succ_b8 cur_clk) pseudo mode tot_clk cur_pc)))
    ]
   ]
  ].

(* ********** *)
(* ESECUZIONE *)
(* ********** *)

let rec execute (m:mcu_type) (t:memory_impl) (s:tick_result (any_status m t)) (n:nat) on n ≝
 match s with
  [ TickERR s' error ⇒ TickERR ? s' error
  | TickSUSP s' susp ⇒ TickSUSP ? s' susp
  | TickOK s'        ⇒ match n with [ O ⇒ TickOK ? s' | S n' ⇒ execute m t (tick m t s') n' ]
  ].

lemma breakpoint:
 ∀m,u,s,n1,n2. execute m u s (n1 + n2) = execute m u (execute m u s n1) n2.
 intros;
 generalize in match s; clear s;
 elim n1 0;
  [ intros;
    cases t;
    reflexivity
  | simplify;
    intros (n K s);
    cases s;
     [ 1,2: simplify;
       cases n2;
       simplify;
       reflexivity;
       | simplify;
         apply K;
     ]
  ]
qed.
