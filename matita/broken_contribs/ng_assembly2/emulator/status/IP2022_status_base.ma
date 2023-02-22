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

include "emulator/memory/memory_struct.ma".
include "num/word16.ma".
include "num/word24.ma".

(* ******************************** *)
(* IP2022 REGISTER SPECIAL HARDWARE *)
(* ******************************** *)

(* (Top Of Stack) : CALLH/CALL ↑ CALLH/CALL ↓ *)
(* Pos2-15        : ...        ↑ ...        ↓ *)
(* Pos16          : 0xFFFF     ↑ ...        ↓ *)
ndefinition aux_callstack_type ≝ Array16T word16.

(* Top Of Stack : 0xFFFF on reset *)
ndefinition new_callstack ≝
 mk_Array16T ? (〈〈xF,xF〉:〈xF,xF〉〉) (〈〈xF,xF〉:〈xF,xF〉〉) (〈〈xF,xF〉:〈xF,xF〉〉) (〈〈xF,xF〉:〈xF,xF〉〉)
               (〈〈xF,xF〉:〈xF,xF〉〉) (〈〈xF,xF〉:〈xF,xF〉〉) (〈〈xF,xF〉:〈xF,xF〉〉) (〈〈xF,xF〉:〈xF,xF〉〉)
               (〈〈xF,xF〉:〈xF,xF〉〉) (〈〈xF,xF〉:〈xF,xF〉〉) (〈〈xF,xF〉:〈xF,xF〉〉) (〈〈xF,xF〉:〈xF,xF〉〉)
               (〈〈xF,xF〉:〈xF,xF〉〉) (〈〈xF,xF〉:〈xF,xF〉〉) (〈〈xF,xF〉:〈xF,xF〉〉) (〈〈xF,xF〉:〈xF,xF〉〉).

ndefinition pop_callstack ≝
λcs:aux_callstack_type.
 pair … (a16_1 ? cs)
        (mk_Array16T ? (a16_2 ? cs)  (a16_3 ? cs)  (a16_4 ? cs)  (a16_5 ? cs)
                       (a16_6 ? cs)  (a16_7 ? cs)  (a16_8 ? cs)  (a16_9 ? cs)
                       (a16_10 ? cs) (a16_11 ? cs) (a16_12 ? cs) (a16_13 ? cs)
                       (a16_14 ? cs) (a16_15 ? cs) (a16_16 ? cs) 〈〈xF,xF〉:〈xF,xF〉〉).

ndefinition push_callstack ≝
λcs:aux_callstack_type.λtop.
 mk_Array16T ? top           (a16_1 ? cs)  (a16_2 ? cs)  (a16_3 ? cs)
               (a16_4 ? cs)  (a16_5 ? cs)  (a16_6 ? cs)  (a16_7 ? cs)
               (a16_8 ? cs)  (a16_9 ? cs)  (a16_10 ? cs) (a16_11 ? cs)
               (a16_12 ? cs) (a16_13 ? cs) (a16_14 ? cs) (a16_15 ? cs).

nlemma callstack_is_comparable : comparable.
 @ (aux_callstack_type)
  ##[ napply (zeroc (ar16_is_comparable word16_is_comparable))
  ##| napply (forallc (ar16_is_comparable word16_is_comparable))
  ##| napply (eqc (ar16_is_comparable word16_is_comparable))
  ##| napply (eqc_to_eq (ar16_is_comparable word16_is_comparable))
  ##| napply (eq_to_eqc (ar16_is_comparable word16_is_comparable))
  ##| napply (neqc_to_neq (ar16_is_comparable word16_is_comparable))
  ##| napply (neq_to_neqc (ar16_is_comparable word16_is_comparable))
  ##| napply (decidable_c (ar16_is_comparable word16_is_comparable))
  ##| napply (symmetric_eqc (ar16_is_comparable word16_is_comparable))
  ##]
nqed.

unification hint 0 ≔ ⊢ carr callstack_is_comparable ≡ aux_callstack_type.

(* array ad accesso diretto di 8 registri ADDR a 24bit *)
(* selezione con registro ADDRSEL, solo i primi 3bit validi *)
ndefinition aux_addrarray_type ≝ Array8T word24.

(* tutti a 0x000000 on reset *)
ndefinition new_addrarray : aux_addrarray_type ≝
 mk_Array8T ? (zeroc ?) (zeroc ?) (zeroc ?) (zeroc ?)
              (zeroc ?) (zeroc ?) (zeroc ?) (zeroc ?).

ndefinition get_addrarray ≝
λaddrsel:byte8.λaa:aux_addrarray_type.
 getn_array8T (oct_of_exL (cnL ? addrsel)) ? aa.

ndefinition set_addrarray ≝
λaddrsel:byte8.λaa:aux_addrarray_type.λv.
 setn_array8T (oct_of_exL (cnL ? addrsel)) ? aa v.

nlemma addrarray_is_comparable : comparable.
 @ (aux_addrarray_type)
  ##[ napply (zeroc (ar8_is_comparable word24_is_comparable))
  ##| napply (forallc (ar8_is_comparable word24_is_comparable))
  ##| napply (eqc (ar8_is_comparable word24_is_comparable))
  ##| napply (eqc_to_eq (ar8_is_comparable word24_is_comparable))
  ##| napply (eq_to_eqc (ar8_is_comparable word24_is_comparable))
  ##| napply (neqc_to_neq (ar8_is_comparable word24_is_comparable))
  ##| napply (neq_to_neqc (ar8_is_comparable word24_is_comparable))
  ##| napply (decidable_c (ar8_is_comparable word24_is_comparable))
  ##| napply (symmetric_eqc (ar8_is_comparable word24_is_comparable))
  ##]
nqed.

unification hint 0 ≔ ⊢ carr addrarray_is_comparable ≡ aux_addrarray_type.

(* *********************************** *)
(* STATUS INTERNO DEL PROCESSORE (ALU) *)
(* *********************************** *)

(* ALU dell'IP2022 *)
nrecord alu_IP2022: Type ≝
 {
 (* W: accumulatore *)
 acc_low_reg_IP2022 : byte8;
 (* MULH: parte alta moltiplicazione *)
 mulh_reg_IP2022 : byte8;

 (* ADDRSEL: selettore di indirizzo *)
 addrsel_reg_IP2022 : byte8;
 (* ADDR [ADDRX|ADDRH|ADDRL] : array indirizzi indicizzati da ADDRSEL *)
 addr_array_IP2022 : aux_addrarray_type;

 (* CALL [CALLH|CALLL] : stack indirizzi di ritorno *)
 call_stack_IP2022 : aux_callstack_type;

 (* IP [IPH|IPL] : indirect pointer *)
 ip_reg_IP2022 : word16;
 (* DP [DPH|DPL] : data pointer *)
 dp_reg_IP2022 : word16;
 (* DATA [DATAH|DATAL] : data value *)
 data_reg_IP2022 : word16;
 (* SP [SPH|SPL] : stack pointer *)
 sp_reg_IP2022 : word16;
 (* PC [PCH|PCL] : program counter *)
 pc_reg_IP2022 : word16;

 (* SPEED[xxxxSSSS] : divisore del clock *)
 speed_reg_IP2022 : exadecim;
 (* PAGE [PPPxxxxx] : selettore pagina *)
 page_reg_IP2022 : oct;

 (* H: flag semi-carry (somma nibble basso) *)
 h_flag_IP2022 : bool;
 (* Z: flag zero *)
 z_flag_IP2022 : bool;
 (* C: flag carry *)
 c_flag_IP2022 : bool;
 
 (* skip mode : effettua fetch-decode, no execute *)
 skip_mode_IP2022 : bool
 }.

notation "{hvbox('W_Reg' ≝ w ; break 'MulH_Reg' ≝ mulh ; break 'Addrsel_Reg' ≝ addrsel ; break 'Addr_Array' ≝ addr ; break 'Call_Stack' ≝ call ; break 'Ip_Reg' ≝ ip ; break 'Dp_Reg' ≝ dp ; break 'Data_Reg' ≝ data ; break 'Sp_Reg' ≝ sp ; break 'Pc_Reg' ≝ pc ; break 'Speed_Reg' ≝ speed ; break 'Page_Reg' ≝ page ; break 'H_Flag' ≝ hfl ; break 'Z_Flag' ≝ zfl ; break 'C_Flag' ≝ cfl ; break 'Skip_Mode' ≝ skipmode)}"
 non associative with precedence 80 for
 @{ 'mk_alu_IP2022 $w $mulh $addrsel $addr $call $ip $dp $data $sp $pc $speed $page $hfl $zfl $cfl $skipmode }.
interpretation "mk_alu_IP2022" 'mk_alu_IP2022 w mulh addrsel addr call ip dp data sp pc speed page hfl zfl cfl skipmode =
 (mk_alu_IP2022 w mulh addrsel addr call ip dp data sp pc speed page hfl zfl cfl skipmode).

(* ****** *)
(* SETTER *)
(* ****** *)

(* setter specifico IP2022 di A *)
ndefinition set_acc_8_low_reg_IP2022 ≝
λalu.λacclow':byte8.
 mk_alu_IP2022
  acclow'
  (mulh_reg_IP2022 alu)
  (addrsel_reg_IP2022 alu)
  (addr_array_IP2022 alu)
  (call_stack_IP2022 alu)
  (ip_reg_IP2022 alu)
  (dp_reg_IP2022 alu)
  (data_reg_IP2022 alu)
  (sp_reg_IP2022 alu)
  (pc_reg_IP2022 alu)
  (speed_reg_IP2022 alu)
  (page_reg_IP2022 alu)
  (h_flag_IP2022 alu)
  (z_flag_IP2022 alu)
  (c_flag_IP2022 alu)
  (skip_mode_IP2022 alu).

(* setter specifico IP2022 di MULH *)
ndefinition set_mulh_reg_IP2022 ≝
λalu.λmulh':byte8.
 mk_alu_IP2022
  (acc_low_reg_IP2022 alu)
  mulh'
  (addrsel_reg_IP2022 alu)
  (addr_array_IP2022 alu)
  (call_stack_IP2022 alu)
  (ip_reg_IP2022 alu)
  (dp_reg_IP2022 alu)
  (data_reg_IP2022 alu)
  (sp_reg_IP2022 alu)
  (pc_reg_IP2022 alu)
  (speed_reg_IP2022 alu)
  (page_reg_IP2022 alu)
  (h_flag_IP2022 alu)
  (z_flag_IP2022 alu)
  (c_flag_IP2022 alu)
  (skip_mode_IP2022 alu).

(* setter specifico IP2022 di ADDRSEL *)
ndefinition set_addrsel_reg_IP2022 ≝
λalu.λaddrsel':byte8.
 mk_alu_IP2022
  (acc_low_reg_IP2022 alu)
  (mulh_reg_IP2022 alu)
  addrsel'
  (addr_array_IP2022 alu)
  (call_stack_IP2022 alu)
  (ip_reg_IP2022 alu)
  (dp_reg_IP2022 alu)
  (data_reg_IP2022 alu)
  (sp_reg_IP2022 alu)
  (pc_reg_IP2022 alu)
  (speed_reg_IP2022 alu)
  (page_reg_IP2022 alu)
  (h_flag_IP2022 alu)
  (z_flag_IP2022 alu)
  (c_flag_IP2022 alu)
  (skip_mode_IP2022 alu).

(* setter specifico IP2022 di ADDR *)
ndefinition set_addr_reg_IP2022 ≝
λalu.λaddr':word24.
 mk_alu_IP2022
  (acc_low_reg_IP2022 alu)
  (mulh_reg_IP2022 alu)
  (addrsel_reg_IP2022 alu)
  (set_addrarray (addrsel_reg_IP2022 alu) (addr_array_IP2022 alu) addr')
  (call_stack_IP2022 alu)
  (ip_reg_IP2022 alu)
  (dp_reg_IP2022 alu)
  (data_reg_IP2022 alu)
  (sp_reg_IP2022 alu)
  (pc_reg_IP2022 alu)
  (speed_reg_IP2022 alu)
  (page_reg_IP2022 alu)
  (h_flag_IP2022 alu)
  (z_flag_IP2022 alu)
  (c_flag_IP2022 alu)
  (skip_mode_IP2022 alu).

ndefinition get_addr_reg_IP2022 ≝
λalu.get_addrarray (addrsel_reg_IP2022 alu) (addr_array_IP2022 alu).

(* setter specifico IP2022 di CALL *)
ndefinition set_call_reg_IP2022 ≝
λalu.λcall':word16.
 mk_alu_IP2022
  (acc_low_reg_IP2022 alu)
  (mulh_reg_IP2022 alu)
  (addrsel_reg_IP2022 alu)
  (addr_array_IP2022 alu)
  (setn_array16T x0 ? (call_stack_IP2022 alu) call')
  (ip_reg_IP2022 alu)
  (dp_reg_IP2022 alu)
  (data_reg_IP2022 alu)
  (sp_reg_IP2022 alu)
  (pc_reg_IP2022 alu)
  (speed_reg_IP2022 alu)
  (page_reg_IP2022 alu)
  (h_flag_IP2022 alu)
  (z_flag_IP2022 alu)
  (c_flag_IP2022 alu)
  (skip_mode_IP2022 alu).

ndefinition get_call_reg_IP2022 ≝
λalu.getn_array16T x0 ? (call_stack_IP2022 alu).

ndefinition set_call_stack_IP2022 ≝
λalu.λcall':aux_callstack_type.
 mk_alu_IP2022
  (acc_low_reg_IP2022 alu)
  (mulh_reg_IP2022 alu)
  (addrsel_reg_IP2022 alu)
  (addr_array_IP2022 alu)
  call'
  (ip_reg_IP2022 alu)
  (dp_reg_IP2022 alu)
  (data_reg_IP2022 alu)
  (sp_reg_IP2022 alu)
  (pc_reg_IP2022 alu)
  (speed_reg_IP2022 alu)
  (page_reg_IP2022 alu)
  (h_flag_IP2022 alu)
  (z_flag_IP2022 alu)
  (c_flag_IP2022 alu)
  (skip_mode_IP2022 alu).

ndefinition push_call_reg_IP2022 ≝
λalu.λcall':word16.
 mk_alu_IP2022
  (acc_low_reg_IP2022 alu)
  (mulh_reg_IP2022 alu)
  (addrsel_reg_IP2022 alu)
  (addr_array_IP2022 alu)
  (push_callstack (call_stack_IP2022 alu) call')
  (ip_reg_IP2022 alu)
  (dp_reg_IP2022 alu)
  (data_reg_IP2022 alu)
  (sp_reg_IP2022 alu)
  (pc_reg_IP2022 alu)
  (speed_reg_IP2022 alu)
  (page_reg_IP2022 alu)
  (h_flag_IP2022 alu)
  (z_flag_IP2022 alu)
  (c_flag_IP2022 alu)
  (skip_mode_IP2022 alu).

ndefinition pop_call_reg_IP2022 ≝
λalu.match pop_callstack (call_stack_IP2022 alu) with
      [ pair val call' ⇒ pair … val (set_call_stack_IP2022 alu call') ].

(* setter specifico IP2022 di IP *)
ndefinition set_ip_reg_IP2022 ≝
λalu.λip':word16.
 mk_alu_IP2022
  (acc_low_reg_IP2022 alu)
  (mulh_reg_IP2022 alu)
  (addrsel_reg_IP2022 alu)
  (addr_array_IP2022 alu)
  (call_stack_IP2022 alu)
  ip'
  (dp_reg_IP2022 alu)
  (data_reg_IP2022 alu)
  (sp_reg_IP2022 alu)
  (pc_reg_IP2022 alu)
  (speed_reg_IP2022 alu)
  (page_reg_IP2022 alu)
  (h_flag_IP2022 alu)
  (z_flag_IP2022 alu)
  (c_flag_IP2022 alu)
  (skip_mode_IP2022 alu).

(* setter specifico IP2022 di DP *)
ndefinition set_dp_reg_IP2022 ≝
λalu.λdp':word16.
 mk_alu_IP2022
  (acc_low_reg_IP2022 alu)
  (mulh_reg_IP2022 alu)
  (addrsel_reg_IP2022 alu)
  (addr_array_IP2022 alu)
  (call_stack_IP2022 alu)
  (ip_reg_IP2022 alu)
  dp'
  (data_reg_IP2022 alu)
  (sp_reg_IP2022 alu)
  (pc_reg_IP2022 alu)
  (speed_reg_IP2022 alu)
  (page_reg_IP2022 alu)
  (h_flag_IP2022 alu)
  (z_flag_IP2022 alu)
  (c_flag_IP2022 alu)
  (skip_mode_IP2022 alu).

(* setter specifico IP2022 di DATA *)
ndefinition set_data_reg_IP2022 ≝
λalu.λdata':word16.
 mk_alu_IP2022
  (acc_low_reg_IP2022 alu)
  (mulh_reg_IP2022 alu)
  (addrsel_reg_IP2022 alu)
  (addr_array_IP2022 alu)
  (call_stack_IP2022 alu)
  (ip_reg_IP2022 alu)
  (dp_reg_IP2022 alu)
  data'
  (sp_reg_IP2022 alu)
  (pc_reg_IP2022 alu)
  (speed_reg_IP2022 alu)
  (page_reg_IP2022 alu)
  (h_flag_IP2022 alu)
  (z_flag_IP2022 alu)
  (c_flag_IP2022 alu)
  (skip_mode_IP2022 alu).

(* setter specifico IP2022 di SP *)
ndefinition set_sp_reg_IP2022 ≝
λalu.λsp':word16.
 mk_alu_IP2022
  (acc_low_reg_IP2022 alu)
  (mulh_reg_IP2022 alu)
  (addrsel_reg_IP2022 alu)
  (addr_array_IP2022 alu)
  (call_stack_IP2022 alu)
  (ip_reg_IP2022 alu)
  (dp_reg_IP2022 alu)
  (data_reg_IP2022 alu)
  sp'
  (pc_reg_IP2022 alu)
  (speed_reg_IP2022 alu)
  (page_reg_IP2022 alu)
  (h_flag_IP2022 alu)
  (z_flag_IP2022 alu)
  (c_flag_IP2022 alu)
  (skip_mode_IP2022 alu).

(* setter specifico IP2022 di PC *)
ndefinition set_pc_reg_IP2022 ≝
λalu.λpc':word16.
 mk_alu_IP2022
  (acc_low_reg_IP2022 alu)
  (mulh_reg_IP2022 alu)
  (addrsel_reg_IP2022 alu)
  (addr_array_IP2022 alu)
  (call_stack_IP2022 alu)
  (ip_reg_IP2022 alu)
  (dp_reg_IP2022 alu)
  (data_reg_IP2022 alu)
  (sp_reg_IP2022 alu)
  pc'
  (speed_reg_IP2022 alu)
  (page_reg_IP2022 alu)
  (h_flag_IP2022 alu)
  (z_flag_IP2022 alu)
  (c_flag_IP2022 alu)
  (skip_mode_IP2022 alu).

(* setter specifico IP2022 di SPEED *)
ndefinition set_speed_reg_IP2022 ≝
λalu.λspeed':exadecim.
 mk_alu_IP2022
  (acc_low_reg_IP2022 alu)
  (mulh_reg_IP2022 alu)
  (addrsel_reg_IP2022 alu)
  (addr_array_IP2022 alu)
  (call_stack_IP2022 alu)
  (ip_reg_IP2022 alu)
  (dp_reg_IP2022 alu)
  (data_reg_IP2022 alu)
  (sp_reg_IP2022 alu)
  (pc_reg_IP2022 alu)
  speed'
  (page_reg_IP2022 alu)
  (h_flag_IP2022 alu)
  (z_flag_IP2022 alu)
  (c_flag_IP2022 alu)
  (skip_mode_IP2022 alu).

(* setter specifico IP2022 di PAGE *)
ndefinition set_page_reg_IP2022 ≝
λalu.λpage':oct.
 mk_alu_IP2022
  (acc_low_reg_IP2022 alu)
  (mulh_reg_IP2022 alu)
  (addrsel_reg_IP2022 alu)
  (addr_array_IP2022 alu)
  (call_stack_IP2022 alu)
  (ip_reg_IP2022 alu)
  (dp_reg_IP2022 alu)
  (data_reg_IP2022 alu)
  (sp_reg_IP2022 alu)
  (pc_reg_IP2022 alu)
  (speed_reg_IP2022 alu)
  page'
  (h_flag_IP2022 alu)
  (z_flag_IP2022 alu)
  (c_flag_IP2022 alu)
  (skip_mode_IP2022 alu).

(* setter specifico IP2022 di H *)
ndefinition set_h_flag_IP2022 ≝
λalu.λhfl':bool.
 mk_alu_IP2022
  (acc_low_reg_IP2022 alu)
  (mulh_reg_IP2022 alu)
  (addrsel_reg_IP2022 alu)
  (addr_array_IP2022 alu)
  (call_stack_IP2022 alu)
  (ip_reg_IP2022 alu)
  (dp_reg_IP2022 alu)
  (data_reg_IP2022 alu)
  (sp_reg_IP2022 alu)
  (pc_reg_IP2022 alu)
  (speed_reg_IP2022 alu)
  (page_reg_IP2022 alu)
  hfl'
  (z_flag_IP2022 alu)
  (c_flag_IP2022 alu)
  (skip_mode_IP2022 alu).

(* setter specifico IP2022 di Z *)
ndefinition set_z_flag_IP2022 ≝
λalu.λzfl':bool.
 mk_alu_IP2022
  (acc_low_reg_IP2022 alu)
  (mulh_reg_IP2022 alu)
  (addrsel_reg_IP2022 alu)
  (addr_array_IP2022 alu)
  (call_stack_IP2022 alu)
  (ip_reg_IP2022 alu)
  (dp_reg_IP2022 alu)
  (data_reg_IP2022 alu)
  (sp_reg_IP2022 alu)
  (pc_reg_IP2022 alu)
  (speed_reg_IP2022 alu)
  (page_reg_IP2022 alu)
  (h_flag_IP2022 alu)
  zfl'
  (c_flag_IP2022 alu)
  (skip_mode_IP2022 alu).

(* setter specifico IP2022 di C *)
ndefinition set_c_flag_IP2022 ≝
λalu.λcfl':bool.
 mk_alu_IP2022
  (acc_low_reg_IP2022 alu)
  (mulh_reg_IP2022 alu)
  (addrsel_reg_IP2022 alu)
  (addr_array_IP2022 alu)
  (call_stack_IP2022 alu)
  (ip_reg_IP2022 alu)
  (dp_reg_IP2022 alu)
  (data_reg_IP2022 alu)
  (sp_reg_IP2022 alu)
  (pc_reg_IP2022 alu)
  (speed_reg_IP2022 alu)
  (page_reg_IP2022 alu)
  (h_flag_IP2022 alu)
  (z_flag_IP2022 alu)
  cfl'
  (skip_mode_IP2022 alu).

(* setter specifico IP2022 di SKIP *)
ndefinition set_skip_mode_IP2022 ≝
λalu.λskipmode':bool.
 mk_alu_IP2022
  (acc_low_reg_IP2022 alu)
  (mulh_reg_IP2022 alu)
  (addrsel_reg_IP2022 alu)
  (addr_array_IP2022 alu)
  (call_stack_IP2022 alu)
  (ip_reg_IP2022 alu)
  (dp_reg_IP2022 alu)
  (data_reg_IP2022 alu)
  (sp_reg_IP2022 alu)
  (pc_reg_IP2022 alu)
  (speed_reg_IP2022 alu)
  (page_reg_IP2022 alu)
  (h_flag_IP2022 alu)
  (z_flag_IP2022 alu)
  (c_flag_IP2022 alu)
  skipmode'.

(* ***************** *)
(* CONFRONTO FRA ALU *)
(* ***************** *)

(* confronto registro per registro dell'IP2022 *)
ndefinition eq_IP2022_alu ≝
λalu1,alu2:alu_IP2022.
 (eqc ? (acc_low_reg_IP2022 alu1) (acc_low_reg_IP2022 alu2)) ⊗
 (eqc ? (mulh_reg_IP2022 alu1) (mulh_reg_IP2022 alu2)) ⊗
 (eqc ? (addrsel_reg_IP2022 alu1) (addrsel_reg_IP2022 alu2)) ⊗
 (eqc ? (addr_array_IP2022 alu1) (addr_array_IP2022 alu2)) ⊗
 (eqc ? (call_stack_IP2022 alu1) (call_stack_IP2022 alu2)) ⊗
 (eqc ? (ip_reg_IP2022 alu1) (ip_reg_IP2022 alu2)) ⊗
 (eqc ? (dp_reg_IP2022 alu1) (dp_reg_IP2022 alu2)) ⊗
 (eqc ? (data_reg_IP2022 alu1) (data_reg_IP2022 alu2)) ⊗
 (eqc ? (sp_reg_IP2022 alu1) (sp_reg_IP2022 alu2)) ⊗
 (eqc ? (pc_reg_IP2022 alu1) (pc_reg_IP2022 alu2)) ⊗
 (eqc ? (speed_reg_IP2022 alu1) (speed_reg_IP2022 alu2)) ⊗
 (eqc ? (page_reg_IP2022 alu1) (page_reg_IP2022 alu2)) ⊗
 (eqc ? (h_flag_IP2022 alu1) (h_flag_IP2022 alu2)) ⊗
 (eqc ? (z_flag_IP2022 alu1) (z_flag_IP2022 alu2)) ⊗
 (eqc ? (c_flag_IP2022 alu1) (c_flag_IP2022 alu2)) ⊗
 (eqc ? (skip_mode_IP2022 alu1) (skip_mode_IP2022 alu2)).

ndefinition forall_IP2022_alu ≝ λP:alu_IP2022 → bool.
 forallc ? (λr1.forallc ? (λr2.
 forallc ? (λr3.forallc ? (λr4.
 forallc ? (λr5.forallc ? (λr6.
 forallc ? (λr7.forallc ? (λr8.
 forallc ? (λr9.forallc ? (λr10.
 forallc ? (λr11.forallc ? (λr12.
 forallc ? (λr13.forallc ? (λr14.
 forallc ? (λr15.forallc ? (λr16.
 P (mk_alu_IP2022 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16))))))))))))))))).
