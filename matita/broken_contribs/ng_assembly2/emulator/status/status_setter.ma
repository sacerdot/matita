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

include "emulator/status/status.ma".

(* ***************************** *)
(* SETTER SPECIFICI FORTI/DEBOLI *)
(* ***************************** *)

(* funzione ausiliaria per il tipaggio dei setter forti *)
ndefinition aux_set_type ≝ λT:Type.λm:mcu_type.aux_alu_type m → T → aux_alu_type m.

(* funzione ausiliaria per il tipaggio dei setter deboli *)
ndefinition aux_set_type_opt ≝ λT:Type.λm:mcu_type.option (aux_set_type T m).

(* DESCRITTORI ESTERNI ALLA ALU *)

(* setter forte della ALU *)
ndefinition set_alu ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λalu'.
 mk_any_status … alu' (mem_desc … s) (chk_desc … s) (clk_desc … s).

(* setter forte della memoria *)
ndefinition set_mem_desc ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λmem':aux_mem_type t.
 mk_any_status … (alu … s) mem' (chk_desc … s) (clk_desc … s).

(* setter forte del descrittore *)
ndefinition set_chk_desc ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λchk':aux_chk_type t.
 mk_any_status … (alu … s) (mem_desc … s) chk' (clk_desc … s).

(* setter forte del clik *)
ndefinition set_clk_desc ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λclk':option (aux_clk_type m).
 mk_any_status … (alu … s) (mem_desc … s) (chk_desc … s) clk'.

(* REGISTRO A *)

(* setter forte di A *)
ndefinition set_acc_8_low_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval:byte8.
 set_alu … s 
 (match m return aux_set_type byte8 with
  [ HC05 ⇒ set_acc_8_low_reg_HC05
  | HC08 ⇒ set_acc_8_low_reg_HC08
  | HCS08 ⇒ set_acc_8_low_reg_HC08
  | RS08 ⇒ set_acc_8_low_reg_RS08
  | IP2022 ⇒ set_acc_8_low_reg_IP2022
  ] (alu … s) val).

(* REGISTRO X *)

ndefinition set_indX_8_low_reg_sHC05 ≝
λt:memory_impl.λs:any_status HC05 t.λval.
 set_alu … s (set_indX_8_low_reg_HC05 (alu … s) val).

ndefinition set_indX_8_low_reg_sHC08 ≝
λt:memory_impl.λs:any_status HC08 t.λval.
 set_alu … s (set_indX_8_low_reg_HC08 (alu … s) val).

ndefinition set_indX_8_low_reg_sHCS08 ≝
λt:memory_impl.λs:any_status HCS08 t.λval.
 set_alu … s (set_indX_8_low_reg_HC08 (alu … s) val).

(* setter forte di X *)
ndefinition set_indX_8_low_reg ≝
λm:mcu_type.λt.
 match m
  return λm.any_status m t → byte8 → option (any_status m t)
 with
  [ HC05 ⇒ λs:any_status ? t.λval.Some ? (set_indX_8_low_reg_sHC05 t s val)
  | HC08 ⇒ λs:any_status ? t.λval.Some ? (set_indX_8_low_reg_sHC08 t s val)
  | HCS08 ⇒ λs:any_status ? t.λval.Some ? (set_indX_8_low_reg_sHCS08 t s val)
  | RS08 ⇒ λs:any_status ? t.λval.None ?
  | IP2022 ⇒ λs:any_status ? t.λval.None ?
  ].

(* setter debole di X *)
ndefinition setweak_indX_8_low_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval.
 match set_indX_8_low_reg … s val with
  [ None ⇒ s | Some s' ⇒ s' ].

(* REGISTRO H *)

ndefinition set_indX_8_high_reg_sHC08 ≝
λt:memory_impl.λs:any_status HC08 t.λval.
 set_alu … s (set_indX_8_high_reg_HC08 (alu … s) val).

ndefinition set_indX_8_high_reg_sHCS08 ≝
λt:memory_impl.λs:any_status HCS08 t.λval.
 set_alu … s (set_indX_8_high_reg_HC08 (alu … s) val).

(* setter forte di H *)
ndefinition set_indX_8_high_reg ≝
λm:mcu_type.λt.
 match m
  return λm.any_status m t → byte8 → option (any_status m t)
 with
  [ HC05 ⇒ λs:any_status ? t.λval.None ?
  | HC08 ⇒ λs:any_status ? t.λval.Some ? (set_indX_8_high_reg_sHC08 t s val)
  | HCS08 ⇒ λs:any_status ? t.λval.Some ? (set_indX_8_high_reg_sHCS08 t s val)
  | RS08 ⇒ λs:any_status ? t.λval.None ?
  | IP2022 ⇒ λs:any_status ? t.λval.None ?
  ].

(* setter debole di H *)
ndefinition setweak_indX_8_high_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval.
 match set_indX_8_high_reg … s val with
  [ None ⇒ s | Some s' ⇒ s' ].

(* REGISTRO H:X *)

ndefinition set_indX_16_reg_sHC08 ≝
λt:memory_impl.λs:any_status HC08 t.λval.
 set_alu … s (set_indX_16_reg_HC08 (alu … s) val).

ndefinition set_indX_16_reg_sHCS08 ≝
λt:memory_impl.λs:any_status HCS08 t.λval.
 set_alu … s (set_indX_16_reg_HC08 (alu … s) val).

(* setter forte di H:X *)
ndefinition set_indX_16_reg ≝
λm:mcu_type.λt.
 match m
  return λm.any_status m t → word16 → option (any_status m t)
 with
  [ HC05 ⇒ λs:any_status ? t.λval.None ?
  | HC08 ⇒ λs:any_status ? t.λval.Some ? (set_indX_16_reg_sHC08 t s val)
  | HCS08 ⇒ λs:any_status ? t.λval.Some ? (set_indX_16_reg_sHCS08 t s val)
  | RS08 ⇒ λs:any_status ? t.λval.None ?
  | IP2022 ⇒ λs:any_status ? t.λval.None ?
  ].

(* setter debole di H:X *)
ndefinition setweak_indX_16_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval.
 match set_indX_16_reg … s val with
  [ None ⇒ s | Some s' ⇒ s' ].

(* REGISTRO SP *)

ndefinition set_sp_reg_sHC05 ≝
λt:memory_impl.λs:any_status HC05 t.λval.
 set_alu … s (set_sp_reg_HC05 (alu … s) val).

ndefinition set_sp_reg_sHC08 ≝
λt:memory_impl.λs:any_status HC08 t.λval.
 set_alu … s (set_sp_reg_HC08 (alu … s) val).

ndefinition set_sp_reg_sHCS08 ≝
λt:memory_impl.λs:any_status HCS08 t.λval.
 set_alu … s (set_sp_reg_HC08 (alu … s) val).

ndefinition set_sp_reg_sIP2022 ≝
λt:memory_impl.λs:any_status IP2022 t.λval.
 set_alu … s (set_sp_reg_IP2022 (alu … s) val).

(* setter forte di SP *)
ndefinition set_sp_reg ≝
λm:mcu_type.λt.
 match m
  return λm.any_status m t → word16 → option (any_status m t)
 with
  [ HC05 ⇒ λs:any_status ? t.λval.Some ? (set_sp_reg_sHC05 t s val)
  | HC08 ⇒ λs:any_status ? t.λval.Some ? (set_sp_reg_sHC08 t s val)
  | HCS08 ⇒ λs:any_status ? t.λval.Some ? (set_sp_reg_sHCS08 t s val)
  | RS08 ⇒ λs:any_status ? t.λval.None ?
  | IP2022 ⇒ λs:any_status ? t.λval.Some ? (set_sp_reg_sIP2022 t s val)
  ].

(* setter debole di SP *)
ndefinition setweak_sp_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval.
 match set_sp_reg … s val with
  [ None ⇒ s | Some s' ⇒ s' ].

(* REGISTRO PC *)

(* setter forte di PC *)
ndefinition set_pc_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λpc':word16.
 set_alu … s 
 (match m return aux_set_type word16 with
  [ HC05 ⇒ set_pc_reg_HC05
  | HC08 ⇒ set_pc_reg_HC08
  | HCS08 ⇒ set_pc_reg_HC08
  | RS08 ⇒ set_pc_reg_RS08
  | IP2022 ⇒ set_pc_reg_IP2022
  ] (alu … s) pc').

(* REGISTRO SPC *)

ndefinition set_spc_reg_sRS08 ≝
λt:memory_impl.λs:any_status RS08 t.λval.
 set_alu … s (set_spc_reg_RS08 (alu … s) val).

(* setter forte di SPC *)
ndefinition set_spc_reg ≝
λm:mcu_type.λt.
 match m
  return λm.any_status m t → word16 → option (any_status m t)
 with
  [ HC05 ⇒ λs:any_status ? t.λval.None ?
  | HC08 ⇒ λs:any_status ? t.λval.None ?
  | HCS08 ⇒ λs:any_status ? t.λval.None ?
  | RS08 ⇒ λs:any_status ? t.λval.Some ? (set_spc_reg_sRS08 t s val)
  | IP2022 ⇒ λs:any_status ? t.λval.None ?
  ].

(* setter debole di SPC *)
ndefinition setweak_spc_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval.
 match set_spc_reg … s val with
  [ None ⇒ s | Some s' ⇒ s' ].

(* REGISTRO MULH *)

ndefinition set_mulh_reg_sIP2022 ≝
λt:memory_impl.λs:any_status IP2022 t.λval.
 set_alu … s (set_mulh_reg_IP2022 (alu … s) val).

(* setter forte di MULH *)
ndefinition set_mulh_reg ≝
λm:mcu_type.λt.
 match m
  return λm.any_status m t → byte8 → option (any_status m t)
 with
  [ HC05 ⇒ λs:any_status ? t.λval.None ?
  | HC08 ⇒ λs:any_status ? t.λval.None ?
  | HCS08 ⇒ λs:any_status ? t.λval.None ?
  | RS08 ⇒ λs:any_status ? t.λval.None ?
  | IP2022 ⇒ λs:any_status ? t.λval.Some ? (set_mulh_reg_sIP2022 t s val)
  ].

(* setter debole di MULH *)
ndefinition setweak_mulh_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval.
 match set_mulh_reg … s val with
  [ None ⇒ s | Some s' ⇒ s' ].

(* REGISTRO ADDRSEL *)

ndefinition set_addrsel_reg_sIP2022 ≝
λt:memory_impl.λs:any_status IP2022 t.λval.
 set_alu … s (set_addrsel_reg_IP2022 (alu … s) val).

(* setter forte di ADDRSEL *)
ndefinition set_addrsel_reg ≝
λm:mcu_type.λt.
 match m
  return λm.any_status m t → byte8 → option (any_status m t)
 with
  [ HC05 ⇒ λs:any_status ? t.λval.None ?
  | HC08 ⇒ λs:any_status ? t.λval.None ?
  | HCS08 ⇒ λs:any_status ? t.λval.None ?
  | RS08 ⇒ λs:any_status ? t.λval.None ?
  | IP2022 ⇒ λs:any_status ? t.λval.Some ? (set_addrsel_reg_sIP2022 t s val)
  ].

(* setter debole di ADDRSEL *)
ndefinition setweak_addrsel_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval.
 match set_addrsel_reg … s val with
  [ None ⇒ s | Some s' ⇒ s' ].

(* REGISTRO ADDR *)

ndefinition set_addr_reg_sIP2022 ≝
λt:memory_impl.λs:any_status IP2022 t.λval.
 set_alu … s (set_addr_reg_IP2022 (alu … s) val).

(* setter forte di ADDR *)
ndefinition set_addr_reg ≝
λm:mcu_type.λt.
 match m
  return λm.any_status m t → word24 → option (any_status m t)
 with
  [ HC05 ⇒ λs:any_status ? t.λval.None ?
  | HC08 ⇒ λs:any_status ? t.λval.None ?
  | HCS08 ⇒ λs:any_status ? t.λval.None ?
  | RS08 ⇒ λs:any_status ? t.λval.None ?
  | IP2022 ⇒ λs:any_status ? t.λval.Some ? (set_addr_reg_sIP2022 t s val)
  ].

(* setter debole di ADDR *)
ndefinition setweak_addr_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval.
 match set_addr_reg … s val with
  [ None ⇒ s | Some s' ⇒ s' ].

(* REGISTRO CALL *)

ndefinition set_call_reg_sIP2022 ≝
λt:memory_impl.λs:any_status IP2022 t.λval.
 set_alu … s (set_call_reg_IP2022 (alu … s) val).

(* setter forte di CALL *)
ndefinition set_call_reg ≝
λm:mcu_type.λt.
 match m
  return λm.any_status m t → word16 → option (any_status m t)
 with
  [ HC05 ⇒ λs:any_status ? t.λval.None ?
  | HC08 ⇒ λs:any_status ? t.λval.None ?
  | HCS08 ⇒ λs:any_status ? t.λval.None ?
  | RS08 ⇒ λs:any_status ? t.λval.None ?
  | IP2022 ⇒ λs:any_status ? t.λval.Some ? (set_call_reg_sIP2022 t s val)
  ].

(* setter debole di CALL *)
ndefinition setweak_call_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval.
 match set_call_reg … s val with
  [ None ⇒ s | Some s' ⇒ s' ].

(* REGISTRO CALL [push] *)

ndefinition push_call_reg_sIP2022 ≝
λt:memory_impl.λs:any_status IP2022 t.λval.
 set_alu … s (push_call_reg_IP2022 (alu … s) val).

(* push forte di CALL *)
ndefinition push_call_reg ≝
λm:mcu_type.λt.
 match m
  return λm.any_status m t → word16 → option (any_status m t)
 with
  [ HC05 ⇒ λs:any_status ? t.λval.None ?
  | HC08 ⇒ λs:any_status ? t.λval.None ?
  | HCS08 ⇒ λs:any_status ? t.λval.None ?
  | RS08 ⇒ λs:any_status ? t.λval.None ?
  | IP2022 ⇒ λs:any_status ? t.λval.Some ? (push_call_reg_sIP2022 t s val)
  ].

(* REGISTRO CALL [pop] *)

ndefinition pop_call_reg_sIP2022 ≝
λt:memory_impl.λs:any_status IP2022 t.
 match pop_call_reg_IP2022 (alu … s) with
  [ pair val alu' ⇒ pair … val (set_alu … s alu') ].

(* pop forte di CALL *)
ndefinition pop_call_reg ≝
λm:mcu_type.λt.
 match m
  return λm.any_status m t → option (ProdT word16 (any_status m t))
 with
  [ HC05 ⇒ λs:any_status ? t.None ?
  | HC08 ⇒ λs:any_status ? t.None ?
  | HCS08 ⇒ λs:any_status ? t.None ?
  | RS08 ⇒ λs:any_status ? t.None ?
  | IP2022 ⇒ λs:any_status ? t.Some ? (pop_call_reg_sIP2022 t s)
  ].

(* REGISTRO IP *)

ndefinition set_ip_reg_sIP2022 ≝
λt:memory_impl.λs:any_status IP2022 t.λval.
 set_alu … s (set_ip_reg_IP2022 (alu … s) val).

(* setter forte di IP *)
ndefinition set_ip_reg ≝
λm:mcu_type.λt.
 match m
  return λm.any_status m t → word16 → option (any_status m t)
 with
  [ HC05 ⇒ λs:any_status ? t.λval.None ?
  | HC08 ⇒ λs:any_status ? t.λval.None ?
  | HCS08 ⇒ λs:any_status ? t.λval.None ?
  | RS08 ⇒ λs:any_status ? t.λval.None ?
  | IP2022 ⇒ λs:any_status ? t.λval.Some ? (set_ip_reg_sIP2022 t s val)
  ].

(* setter debole di IP *)
ndefinition setweak_ip_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval.
 match set_ip_reg … s val with
  [ None ⇒ s | Some s' ⇒ s' ].

(* REGISTRO DP *)

ndefinition set_dp_reg_sIP2022 ≝
λt:memory_impl.λs:any_status IP2022 t.λval.
 set_alu … s (set_dp_reg_IP2022 (alu … s) val).

(* setter forte di DP *)
ndefinition set_dp_reg ≝
λm:mcu_type.λt.
 match m
  return λm.any_status m t → word16 → option (any_status m t)
 with
  [ HC05 ⇒ λs:any_status ? t.λval.None ?
  | HC08 ⇒ λs:any_status ? t.λval.None ?
  | HCS08 ⇒ λs:any_status ? t.λval.None ?
  | RS08 ⇒ λs:any_status ? t.λval.None ?
  | IP2022 ⇒ λs:any_status ? t.λval.Some ? (set_dp_reg_sIP2022 t s val)
  ].

(* setter debole di DP *)
ndefinition setweak_dp_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval.
 match set_dp_reg … s val with
  [ None ⇒ s | Some s' ⇒ s' ].

(* REGISTRO DATA *)

ndefinition set_data_reg_sIP2022 ≝
λt:memory_impl.λs:any_status IP2022 t.λval.
 set_alu … s (set_data_reg_IP2022 (alu … s) val).

(* setter forte di DATA *)
ndefinition set_data_reg ≝
λm:mcu_type.λt.
 match m
  return λm.any_status m t → word16 → option (any_status m t)
 with
  [ HC05 ⇒ λs:any_status ? t.λval.None ?
  | HC08 ⇒ λs:any_status ? t.λval.None ?
  | HCS08 ⇒ λs:any_status ? t.λval.None ?
  | RS08 ⇒ λs:any_status ? t.λval.None ?
  | IP2022 ⇒ λs:any_status ? t.λval.Some ? (set_data_reg_sIP2022 t s val)
  ].

(* setter debole di DATA *)
ndefinition setweak_data_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval.
 match set_data_reg … s val with
  [ None ⇒ s | Some s' ⇒ s' ].

(* REGISTRO SPEED *)

ndefinition set_speed_reg_sIP2022 ≝
λt:memory_impl.λs:any_status IP2022 t.λval.
 set_alu … s (set_speed_reg_IP2022 (alu … s) val).

(* setter forte di SPEED *)
ndefinition set_speed_reg ≝
λm:mcu_type.λt.
 match m
  return λm.any_status m t → exadecim → option (any_status m t)
 with
  [ HC05 ⇒ λs:any_status ? t.λval.None ?
  | HC08 ⇒ λs:any_status ? t.λval.None ?
  | HCS08 ⇒ λs:any_status ? t.λval.None ?
  | RS08 ⇒ λs:any_status ? t.λval.None ?
  | IP2022 ⇒ λs:any_status ? t.λval.Some ? (set_speed_reg_sIP2022 t s val)
  ].

(* setter debole di SPEED *)
ndefinition setweak_speed_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval.
 match set_speed_reg … s val with
  [ None ⇒ s | Some s' ⇒ s' ].

(* REGISTRO PAGE *)

ndefinition set_page_reg_sIP2022 ≝
λt:memory_impl.λs:any_status IP2022 t.λval.
 set_alu … s (set_page_reg_IP2022 (alu … s) val).

(* setter forte di PAGE *)
ndefinition set_page_reg ≝
λm:mcu_type.λt.
 match m
  return λm.any_status m t → oct → option (any_status m t)
 with
  [ HC05 ⇒ λs:any_status ? t.λval.None ?
  | HC08 ⇒ λs:any_status ? t.λval.None ?
  | HCS08 ⇒ λs:any_status ? t.λval.None ?
  | RS08 ⇒ λs:any_status ? t.λval.None ?
  | IP2022 ⇒ λs:any_status ? t.λval.Some ? (set_page_reg_sIP2022 t s val)
  ].

(* setter debole di PAGE *)
ndefinition setweak_page_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval.
 match set_page_reg … s val with
  [ None ⇒ s | Some s' ⇒ s' ].

(* REGISTRO MEMORY MAPPED X *)

ndefinition set_x_map_sRS08 ≝
λt:memory_impl.λs:any_status RS08 t.λval.
 set_alu … s (set_x_map_RS08 (alu … s) val).

(* setter forte di memory mapped X *)
ndefinition set_x_map ≝
λm:mcu_type.λt.
 match m
  return λm.any_status m t → byte8 → option (any_status m t)
 with
  [ HC05 ⇒ λs:any_status ? t.λval.None ?
  | HC08 ⇒ λs:any_status ? t.λval.None ?
  | HCS08 ⇒ λs:any_status ? t.λval.None ?
  | RS08 ⇒ λs:any_status ? t.λval.Some ? (set_x_map_sRS08 t s val)
  | IP2022 ⇒ λs:any_status ? t.λval.None ?
  ].

(* setter debole di memory mapped X *)
ndefinition setweak_x_map ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval.
 match set_x_map … s val with
  [ None ⇒ s | Some s' ⇒ s' ].

(* REGISTRO MEMORY MAPPED PS *)

ndefinition set_ps_map_sRS08 ≝
λt:memory_impl.λs:any_status RS08 t.λval.
 set_alu … s (set_ps_map_RS08 (alu … s) val).

(* setter forte di memory mapped PS *)
ndefinition set_ps_map ≝
λm:mcu_type.λt.
 match m
  return λm.any_status m t → byte8 → option (any_status m t)
 with
  [ HC05 ⇒ λs:any_status ? t.λval.None ?
  | HC08 ⇒ λs:any_status ? t.λval.None ?
  | HCS08 ⇒ λs:any_status ? t.λval.None ?
  | RS08 ⇒ λs:any_status ? t.λval.Some ? (set_ps_map_sRS08 t s val)
  | IP2022 ⇒ λs:any_status ? t.λval.None ?
  ].

(* setter debole di memory mapped PS *)
ndefinition setweak_ps_map ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval.
 match set_ps_map … s val with
  [ None ⇒ s | Some s' ⇒ s' ].

(* MODALITA SKIP *)

ndefinition set_skip_mode_sIP2022 ≝
λt:memory_impl.λs:any_status IP2022 t.λval.
 set_alu … s (set_skip_mode_IP2022 (alu … s) val).

(* setter forte di modalita SKIP *)
ndefinition set_skip_mode ≝
λm:mcu_type.λt.
 match m
  return λm.any_status m t → bool → option (any_status m t)
 with
  [ HC05 ⇒ λs:any_status ? t.λval.None ?
  | HC08 ⇒ λs:any_status ? t.λval.None ?
  | HCS08 ⇒ λs:any_status ? t.λval.None ?
  | RS08 ⇒ λs:any_status ? t.λval.None ?
  | IP2022 ⇒ λs:any_status ? t.λval.Some ? (set_skip_mode_sIP2022 t s val)
  ].

(* setter debole  di SKIP *)
ndefinition setweak_skip_mode ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval.
 match set_skip_mode … s val with
  [ None ⇒ s | Some s' ⇒ s' ].

(* FLAG V *)

ndefinition set_v_flag_sHC08 ≝
λt:memory_impl.λs:any_status HC08 t.λval.
 set_alu … s (set_v_flag_HC08 (alu … s) val).

ndefinition set_v_flag_sHCS08 ≝
λt:memory_impl.λs:any_status HCS08 t.λval.
 set_alu … s (set_v_flag_HC08 (alu … s) val).

(* setter forte di V *)
ndefinition set_v_flag ≝
λm:mcu_type.λt.
 match m
  return λm.any_status m t → bool → option (any_status m t)
 with
  [ HC05 ⇒ λs:any_status ? t.λval.None ?
  | HC08 ⇒ λs:any_status ? t.λval.Some ? (set_v_flag_sHC08 t s val)
  | HCS08 ⇒ λs:any_status ? t.λval.Some ? (set_v_flag_sHCS08 t s val)
  | RS08 ⇒ λs:any_status ? t.λval.None ?
  | IP2022 ⇒ λs:any_status ? t.λval.None ?
  ].

(* setter debole  di V *)
ndefinition setweak_v_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval.
 match set_v_flag … s val with
  [ None ⇒ s | Some s' ⇒ s' ].

(* FLAG H *)

ndefinition set_h_flag_sHC05 ≝
λt:memory_impl.λs:any_status HC05 t.λval.
 set_alu … s (set_h_flag_HC05 (alu … s) val).

ndefinition set_h_flag_sHC08 ≝
λt:memory_impl.λs:any_status HC08 t.λval.
 set_alu … s (set_h_flag_HC08 (alu … s) val).

ndefinition set_h_flag_sHCS08 ≝
λt:memory_impl.λs:any_status HCS08 t.λval.
 set_alu … s (set_h_flag_HC08 (alu … s) val).

ndefinition set_h_flag_sIP2022 ≝
λt:memory_impl.λs:any_status IP2022 t.λval.
 set_alu … s (set_h_flag_IP2022 (alu … s) val).

(* setter forte di H *)
ndefinition set_h_flag ≝
λm:mcu_type.λt.
 match m
  return λm.any_status m t → bool → option (any_status m t)
 with
  [ HC05 ⇒ λs:any_status ? t.λval.Some ? (set_h_flag_sHC05 t s val)
  | HC08 ⇒ λs:any_status ? t.λval.Some ? (set_h_flag_sHC08 t s val)
  | HCS08 ⇒ λs:any_status ? t.λval.Some ? (set_h_flag_sHCS08 t s val)
  | RS08 ⇒ λs:any_status ? t.λval.None ?
  | IP2022 ⇒ λs:any_status ? t.λval.Some ? (set_h_flag_sIP2022 t s val)
  ].

(* setter debole di H *)
ndefinition setweak_h_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval.
 match set_h_flag … s val with
  [ None ⇒ s | Some s' ⇒ s' ].

(* FLAG I *)

ndefinition set_i_flag_sHC05 ≝
λt:memory_impl.λs:any_status HC05 t.λval.
 set_alu … s (set_i_flag_HC05 (alu … s) val).

ndefinition set_i_flag_sHC08 ≝
λt:memory_impl.λs:any_status HC08 t.λval.
 set_alu … s (set_i_flag_HC08 (alu … s) val).

ndefinition set_i_flag_sHCS08 ≝
λt:memory_impl.λs:any_status HCS08 t.λval.
 set_alu … s (set_i_flag_HC08 (alu … s) val).

(* setter forte di I *)
ndefinition set_i_flag ≝
λm:mcu_type.λt.
 match m
  return λm.any_status m t → bool → option (any_status m t)
 with
  [ HC05 ⇒ λs:any_status ? t.λval.Some ? (set_i_flag_sHC05 t s val)
  | HC08 ⇒ λs:any_status ? t.λval.Some ? (set_i_flag_sHC08 t s val)
  | HCS08 ⇒ λs:any_status ? t.λval.Some ? (set_i_flag_sHCS08 t s val)
  | RS08 ⇒ λs:any_status ? t.λval.None ?
  | IP2022 ⇒ λs:any_status ? t.λval.None ?
  ].

(* setter debole di I *)
ndefinition setweak_i_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval.
 match set_i_flag … s val with
  [ None ⇒ s | Some s' ⇒ s' ].

(* FLAG N *)

ndefinition set_n_flag_sHC05 ≝
λt:memory_impl.λs:any_status HC05 t.λval.
 set_alu … s (set_n_flag_HC05 (alu … s) val).

ndefinition set_n_flag_sHC08 ≝
λt:memory_impl.λs:any_status HC08 t.λval.
 set_alu … s (set_n_flag_HC08 (alu … s) val).

ndefinition set_n_flag_sHCS08 ≝
λt:memory_impl.λs:any_status HCS08 t.λval.
 set_alu … s (set_n_flag_HC08 (alu … s) val).

(* setter forte di N *)
ndefinition set_n_flag ≝
λm:mcu_type.λt.
 match m
  return λm.any_status m t → bool → option (any_status m t)
 with
  [ HC05 ⇒ λs:any_status ? t.λval.Some ? (set_n_flag_sHC05 t s val)
  | HC08 ⇒ λs:any_status ? t.λval.Some ? (set_n_flag_sHC08 t s val)
  | HCS08 ⇒ λs:any_status ? t.λval.Some ? (set_n_flag_sHCS08 t s val)
  | RS08 ⇒ λs:any_status ? t.λval.None ?
  | IP2022 ⇒ λs:any_status ? t.λval.None ?
  ].

(* setter debole di N *)
ndefinition setweak_n_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval.
 match set_n_flag … s val with
  [ None ⇒ s | Some s' ⇒ s' ].

(* FLAG Z *)

(* setter forte di Z *)
ndefinition set_z_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λzfl':bool.
 set_alu m t s 
 (match m return aux_set_type bool with
  [ HC05 ⇒ set_z_flag_HC05
  | HC08 ⇒ set_z_flag_HC08
  | HCS08 ⇒ set_z_flag_HC08
  | RS08 ⇒ set_z_flag_RS08
  | IP2022 ⇒ set_z_flag_IP2022
  ] (alu m t s) zfl').

(* FLAG C *)

(* setter forte di C *)
ndefinition set_c_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcfl':bool.
 set_alu m t s 
 (match m return aux_set_type bool with
  [ HC05 ⇒ set_c_flag_HC05
  | HC08 ⇒ set_c_flag_HC08
  | HCS08 ⇒ set_c_flag_HC08
  | RS08 ⇒ set_c_flag_RS08
  | IP2022 ⇒ set_c_flag_IP2022
  ] (alu m t s) cfl').

(* FLAG IRQ *)

ndefinition set_irq_flag_sHC05 ≝
λt:memory_impl.λs:any_status HC05 t.λval.
 set_alu … s (set_irq_flag_HC05 (alu … s) val).

ndefinition set_irq_flag_sHC08 ≝
λt:memory_impl.λs:any_status HC08 t.λval.
 set_alu … s (set_irq_flag_HC08 (alu … s) val).

ndefinition set_irq_flag_sHCS08 ≝
λt:memory_impl.λs:any_status HCS08 t.λval.
 set_alu … s (set_irq_flag_HC08 (alu … s) val).

(* setter forte di IRQ *)
ndefinition set_irq_flag ≝
λm:mcu_type.λt.
 match m
  return λm.any_status m t → bool → option (any_status m t)
 with
  [ HC05 ⇒ λs:any_status ? t.λval.Some ? (set_irq_flag_sHC05 t s val)
  | HC08 ⇒ λs:any_status ? t.λval.Some ? (set_irq_flag_sHC08 t s val)
  | HCS08 ⇒ λs:any_status ? t.λval.Some ? (set_irq_flag_sHCS08 t s val)
  | RS08 ⇒ λs:any_status ? t.λval.None ?
  | IP2022 ⇒ λs:any_status ? t.λval.None ?
  ].

(* setter debole di IRQ *)
ndefinition setweak_irq_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λval.
 match set_irq_flag … s val with
  [ None ⇒ s | Some s' ⇒ s' ].
