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

include "emulator/status/status_setter.ma".

(* **************** *)
(* GETTER SPECIFICI *)
(* **************** *)

(* funzione ausiliaria per il tipaggio dei getter *)
ndefinition aux_get_type ≝ λx:Type.λm:mcu_type.match m with
 [ HC05 ⇒ alu_HC05 | HC08 ⇒ alu_HC08 | HCS08 ⇒ alu_HC08 | RS08 ⇒ alu_RS08
 | IP2022 ⇒ alu_IP2022 ] → x.

(* REGISTRI *)

(* getter di A, esiste sempre *)
ndefinition get_acc_8_low_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type byte8 with
 [ HC05 ⇒ acc_low_reg_HC05
 | HC08 ⇒ acc_low_reg_HC08
 | HCS08 ⇒ acc_low_reg_HC08
 | RS08 ⇒ acc_low_reg_RS08
 | IP2022 ⇒ acc_low_reg_IP2022 ]
 (alu m t s).

(* getter di X, non esiste sempre *)
ndefinition get_indX_8_low_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type (option byte8) with 
 [ HC05 ⇒ λalu.Some ? (indX_low_reg_HC05 alu)
 | HC08 ⇒ λalu.Some ? (indX_low_reg_HC08 alu)
 | HCS08 ⇒ λalu.Some ? (indX_low_reg_HC08 alu)
 | RS08 ⇒ λalu.None ?
 | IP2022 ⇒ λalu.None ? ]
 (alu m t s).

(* getter di H, non esiste sempre *)
ndefinition get_indX_8_high_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type (option byte8) with 
 [ HC05 ⇒ λalu.None ?
 | HC08 ⇒ λalu.Some ? (indX_high_reg_HC08 alu)
 | HCS08 ⇒ λalu.Some ? (indX_high_reg_HC08 alu)
 | RS08 ⇒ λalu.None ?
 | IP2022 ⇒ λalu.None ? ]
 (alu m t s).

(* getter di H:X, non esiste sempre *)
ndefinition get_indX_16_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type (option word16) with 
 [ HC05 ⇒ λalu.None ?
 | HC08 ⇒ λalu.Some ? (mk_word16 (indX_high_reg_HC08 alu) (indX_low_reg_HC08 alu))
 | HCS08 ⇒ λalu.Some ? (mk_word16 (indX_high_reg_HC08 alu) (indX_low_reg_HC08 alu))
 | RS08 ⇒ λalu.None ?
 | IP2022 ⇒ λalu.None ? ]
 (alu m t s).

(* getter di SP, non esiste sempre *)
ndefinition get_sp_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type (option word16) with 
 [ HC05 ⇒ λalu.Some ? (sp_reg_HC05 alu)
 | HC08 ⇒ λalu.Some ? (sp_reg_HC08 alu)
 | HCS08 ⇒ λalu.Some ? (sp_reg_HC08 alu)
 | RS08 ⇒ λalu.None ?
 | IP2022 ⇒ λalu.Some ? (sp_reg_IP2022 alu) ]
 (alu m t s).

(* getter di PC, esiste sempre *)
ndefinition get_pc_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type word16 with 
 [ HC05 ⇒ pc_reg_HC05
 | HC08 ⇒ pc_reg_HC08
 | HCS08 ⇒ pc_reg_HC08
 | RS08 ⇒ pc_reg_RS08
 | IP2022 ⇒ pc_reg_IP2022 ]
 (alu m t s).

(* getter di SPC, non esiste sempre *)
ndefinition get_spc_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type (option word16) with 
 [ HC05 ⇒ λalu.None ?
 | HC08 ⇒ λalu.None ?
 | HCS08 ⇒ λalu.None ?
 | RS08 ⇒ λalu.Some ? (spc_reg_RS08 alu)
 | IP2022 ⇒ λalu.None ? ]
 (alu m t s).

(* getter di MULH, non esiste sempre *)
ndefinition get_mulh_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type (option byte8) with 
 [ HC05 ⇒ λalu.None ?
 | HC08 ⇒ λalu.None ?
 | HCS08 ⇒ λalu.None ?
 | RS08 ⇒ λalu.None ?
 | IP2022 ⇒ λalu.Some ? (mulh_reg_IP2022 alu) ]
 (alu m t s).

(* getter di ADDRSEL, non esiste sempre *)
ndefinition get_addrsel_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type (option byte8) with 
 [ HC05 ⇒ λalu.None ?
 | HC08 ⇒ λalu.None ?
 | HCS08 ⇒ λalu.None ?
 | RS08 ⇒ λalu.None ?
 | IP2022 ⇒ λalu.Some ? (addrsel_reg_IP2022 alu) ]
 (alu m t s).

(* getter di ADDR, non esiste sempre *)
ndefinition get_addr_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type (option word24) with 
 [ HC05 ⇒ λalu.None ?
 | HC08 ⇒ λalu.None ?
 | HCS08 ⇒ λalu.None ?
 | RS08 ⇒ λalu.None ?
 | IP2022 ⇒ λalu.Some ? (get_addr_reg_IP2022 alu) ]
 (alu m t s).

(* getter di CALL, non esiste sempre *)
ndefinition get_call_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type (option word16) with 
 [ HC05 ⇒ λalu.None ?
 | HC08 ⇒ λalu.None ?
 | HCS08 ⇒ λalu.None ?
 | RS08 ⇒ λalu.None ?
 | IP2022 ⇒ λalu.Some ? (get_call_reg_IP2022 alu) ]
 (alu m t s).

(* getter di IP, non esiste sempre *)
ndefinition get_ip_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type (option word16) with 
 [ HC05 ⇒ λalu.None ?
 | HC08 ⇒ λalu.None ?
 | HCS08 ⇒ λalu.None ?
 | RS08 ⇒ λalu.None ?
 | IP2022 ⇒ λalu.Some ? (ip_reg_IP2022 alu) ]
 (alu m t s).

(* getter di DP, non esiste sempre *)
ndefinition get_dp_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type (option word16) with 
 [ HC05 ⇒ λalu.None ?
 | HC08 ⇒ λalu.None ?
 | HCS08 ⇒ λalu.None ?
 | RS08 ⇒ λalu.None ?
 | IP2022 ⇒ λalu.Some ? (dp_reg_IP2022 alu) ]
 (alu m t s).

(* getter di DATA, non esiste sempre *)
ndefinition get_data_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type (option word16) with 
 [ HC05 ⇒ λalu.None ?
 | HC08 ⇒ λalu.None ?
 | HCS08 ⇒ λalu.None ?
 | RS08 ⇒ λalu.None ?
 | IP2022 ⇒ λalu.Some ? (data_reg_IP2022 alu) ]
 (alu m t s).

(* getter di SPEED, non esiste sempre *)
ndefinition get_speed_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type (option exadecim) with 
 [ HC05 ⇒ λalu.None ?
 | HC08 ⇒ λalu.None ?
 | HCS08 ⇒ λalu.None ?
 | RS08 ⇒ λalu.None ?
 | IP2022 ⇒ λalu.Some ? (speed_reg_IP2022 alu) ]
 (alu m t s).

(* getter di PAGE, non esiste sempre *)
ndefinition get_page_reg ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type (option oct) with 
 [ HC05 ⇒ λalu.None ?
 | HC08 ⇒ λalu.None ?
 | HCS08 ⇒ λalu.None ?
 | RS08 ⇒ λalu.None ?
 | IP2022 ⇒ λalu.Some ? (page_reg_IP2022 alu) ]
 (alu m t s).

(* REGISTRI SPECIALI *)

(* getter di memory mapped X, non esiste sempre *)
ndefinition get_x_map ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type (option byte8) with 
 [ HC05 ⇒ λalu.None ?
 | HC08 ⇒ λalu.None ?
 | HCS08 ⇒ λalu.None ?
 | RS08 ⇒ λalu.Some ? (x_map_RS08 alu)
 | IP2022 ⇒ λalu.None ? ]
 (alu m t s).

(* getter di memory mapped PS, non esiste sempre *)
ndefinition get_ps_map ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type (option byte8) with 
 [ HC05 ⇒ λalu.None ?
 | HC08 ⇒ λalu.None ?
 | HCS08 ⇒ λalu.None ?
 | RS08 ⇒ λalu.Some ? (ps_map_RS08 alu)
 | IP2022 ⇒ λalu.None ? ]
 (alu m t s).

(* getter di skip mode, non esiste sempre *)
ndefinition get_skip_mode ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type (option bool) with 
 [ HC05 ⇒ λalu.None ?
 | HC08 ⇒ λalu.None ?
 | HCS08 ⇒ λalu.None ?
 | RS08 ⇒ λalu.None ?
 | IP2022 ⇒ λalu.Some ? (skip_mode_IP2022 alu) ]
 (alu m t s).

(* FLAG *)

(* getter di V, non esiste sempre *)
ndefinition get_v_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type (option bool) with 
 [ HC05 ⇒ λalu.None ?
 | HC08 ⇒ λalu.Some ? (v_flag_HC08 alu)
 | HCS08 ⇒ λalu.Some ? (v_flag_HC08 alu)
 | RS08 ⇒ λalu.None ?
 | IP2022 ⇒ λalu.None ? ]
 (alu m t s).

(* getter di H, non esiste sempre *)
ndefinition get_h_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type (option bool) with 
 [ HC05 ⇒ λalu.Some ? (h_flag_HC05 alu)
 | HC08 ⇒ λalu.Some ? (h_flag_HC08 alu)
 | HCS08 ⇒ λalu.Some ? (h_flag_HC08 alu)
 | RS08 ⇒ λalu.None ?
 | IP2022 ⇒ λalu.Some ? (h_flag_IP2022 alu) ]
 (alu m t s).

(* getter di I, non esiste sempre *)
ndefinition get_i_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type (option bool) with 
 [ HC05 ⇒ λalu.Some ? (i_flag_HC05 alu)
 | HC08 ⇒ λalu.Some ? (i_flag_HC08 alu)
 | HCS08 ⇒ λalu.Some ? (i_flag_HC08 alu)
 | RS08 ⇒ λalu.None ?
 | IP2022 ⇒ λalu.None ? ]
 (alu m t s).

(* getter di N, non esiste sempre *)
ndefinition get_n_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type (option bool) with 
 [ HC05 ⇒ λalu.Some ? (n_flag_HC05 alu)
 | HC08 ⇒ λalu.Some ? (n_flag_HC08 alu)
 | HCS08 ⇒ λalu.Some ? (n_flag_HC08 alu)
 | RS08 ⇒ λalu.None ?
 | IP2022 ⇒ λalu.None ? ]
 (alu m t s).

(* getter di Z, esiste sempre *)
ndefinition get_z_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type bool with 
 [ HC05 ⇒ z_flag_HC05
 | HC08 ⇒ z_flag_HC08
 | HCS08 ⇒ z_flag_HC08
 | RS08 ⇒ z_flag_RS08
 | IP2022 ⇒ z_flag_IP2022 ]
 (alu m t s).

(* getter di C, esiste sempre *)
ndefinition get_c_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type bool with 
 [ HC05 ⇒ c_flag_HC05
 | HC08 ⇒ c_flag_HC08
 | HCS08 ⇒ c_flag_HC08
 | RS08 ⇒ c_flag_RS08
 | IP2022 ⇒ c_flag_IP2022 ]
 (alu m t s).

(* getter di IRQ, non esiste sempre *)
ndefinition get_irq_flag ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m
  return aux_get_type (option bool) with 
 [ HC05 ⇒ λalu.Some ? (irq_flag_HC05 alu)
 | HC08 ⇒ λalu.Some ? (irq_flag_HC08 alu)
 | HCS08 ⇒ λalu.Some ? (irq_flag_HC08 alu)
 | RS08 ⇒ λalu.None ?
 | IP2022 ⇒ λalu.None ? ]
 (alu m t s).
