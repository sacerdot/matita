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

include "num/word16.ma".

(* *********************************** *)
(* STATUS INTERNO DEL PROCESSORE (ALU) *)
(* *********************************** *)

(* ALU dell'RS08 *)
nrecord alu_RS08: Type ≝
 {
 (* A: registo accumulatore *)
 acc_low_reg_RS08 : byte8;
 (* PC: registro program counter *)
 pc_reg_RS08 : word16;
 (* modificatore di PC: per esempio e' definito come 00xxxxxxxxxxxxxxb *)
 (* la logica della sua costruzione e' quindi (PC∧mask) *)
 (* totalmente racchiusa nella ALU, bastera' fare get(set(PC)) *)
 pc_mask_RS08 : word16;
 (* SPC: registro shadow program counter *)
 (* NB: il suo modificatore e' lo stesso di PC *)
 spc_reg_RS08 : word16;

 (* X: registro indice parte bassa *)
 (* NB: in realta' e' mappato in memoria e non risiede nella ALU *)
 (* la lettura/scrittura avviene tramite la locazione [0x000F] *)
 x_map_RS08 : byte8;
 (* PS: registro selezione di pagina *)
 (* serve a indirizzare la finestra RAM di 64b [0x00C0-0x00FF] *)
 (* su tutta la memoria installata [0x0000-0x3FFF]: [00pp pppp ppxx xxxx] *)
 (* NB: in realta' e' mappato in memoria e non risiede nella ALU *)
 (* la lettura/scrittura avviene tramite la locazione [0x001F] *)
 ps_map_RS08 : byte8;
 
 (* Z: flag zero *)
 z_flag_RS08 : bool;
 (* C: flag carry *)
 c_flag_RS08 : bool
 }.

notation "{hvbox('A_Reg' ≝ acclow ; break 'Pc_Reg' ≝ pc ; break 'Pc_Mask' ≝ pcm ; break 'Spc_Reg' ≝ spc ; break 'X_Map' ≝ xm ; break 'Ps_Map' ≝ psm ; break 'Z_Flag' ≝ zfl ; break 'C_Flag' ≝ cfl)}"
 non associative with precedence 80 for
 @{ 'mk_alu_RS08 $acclow $pc $pcm $spc $xm $psm $zfl $cfl }.
interpretation "mk_alu_RS08" 'mk_alu_RS08 acclow pc pcm spc xm psm zfl cfl =
 (mk_alu_RS08 acclow pc pcm spc xm psm zfl cfl).

(* ****** *)
(* SETTER *)
(* ****** *)

(* setter specifico RS08 di A *)
ndefinition set_acc_8_low_reg_RS08 ≝ 
λalu.λacclow':byte8.
 mk_alu_RS08
  acclow'
  (pc_reg_RS08 alu)
  (pc_mask_RS08 alu)
  (spc_reg_RS08 alu)
  (x_map_RS08 alu)
  (ps_map_RS08 alu)
  (z_flag_RS08 alu)
  (c_flag_RS08 alu).

(* setter specifico RS08 di PC, effettua PC∧mask *)
ndefinition set_pc_reg_RS08 ≝ 
λalu.λpc':word16.
 mk_alu_RS08
  (acc_low_reg_RS08 alu)
  (and_w16 pc' (pc_mask_RS08 alu))
  (pc_mask_RS08 alu)
  (spc_reg_RS08 alu)
  (x_map_RS08 alu)
  (ps_map_RS08 alu)
  (z_flag_RS08 alu)
  (c_flag_RS08 alu).

(* setter specifico RS08 di SPC, effettua SPC∧mask *)
ndefinition set_spc_reg_RS08 ≝ 
λalu.λspc':word16.
 mk_alu_RS08
  (acc_low_reg_RS08 alu)
  (pc_reg_RS08 alu)
  (pc_mask_RS08 alu)
  (and_w16 spc' (pc_mask_RS08 alu))
  (x_map_RS08 alu)
  (ps_map_RS08 alu)
  (z_flag_RS08 alu)
  (c_flag_RS08 alu).

(* setter specifico RS08 di memory mapped X *)
ndefinition set_x_map_RS08 ≝ 
λalu.λxm':byte8.
 mk_alu_RS08
  (acc_low_reg_RS08 alu)
  (pc_reg_RS08 alu)
  (pc_mask_RS08 alu)
  (spc_reg_RS08 alu)
  xm'
  (ps_map_RS08 alu)
  (z_flag_RS08 alu)
  (c_flag_RS08 alu).

(* setter specifico RS08 di memory mapped PS *)
ndefinition set_ps_map_RS08 ≝ 
λalu.λpsm':byte8.
 mk_alu_RS08
  (acc_low_reg_RS08 alu)
  (pc_reg_RS08 alu)
  (pc_mask_RS08 alu)
  (spc_reg_RS08 alu)
  (x_map_RS08 alu)
  psm'
  (z_flag_RS08 alu)
  (c_flag_RS08 alu).

(* setter sprcifico RS08 di Z *)
ndefinition set_z_flag_RS08 ≝ 
λalu.λzfl':bool.
 mk_alu_RS08
  (acc_low_reg_RS08 alu)
  (pc_reg_RS08 alu)
  (pc_mask_RS08 alu)
  (spc_reg_RS08 alu)
  (x_map_RS08 alu)
  (ps_map_RS08 alu)
  zfl'
  (c_flag_RS08 alu).

(* setter specifico RS08 di C *)
ndefinition set_c_flag_RS08 ≝ 
λalu.λcfl':bool.
 mk_alu_RS08
  (acc_low_reg_RS08 alu)
  (pc_reg_RS08 alu)
  (pc_mask_RS08 alu)
  (spc_reg_RS08 alu)
  (x_map_RS08 alu)
  (ps_map_RS08 alu)
  (z_flag_RS08 alu)
  cfl'.

(* ***************** *)
(* CONFRONTO FRA ALU *)
(* ***************** *)

(* confronto registro per registro dell'RS08 *)
ndefinition eq_RS08_alu ≝
λalu1,alu2:alu_RS08.
 (eq_b8 (acc_low_reg_RS08 alu1) (acc_low_reg_RS08 alu2)) ⊗
 (eq_w16 (pc_reg_RS08 alu1) (pc_reg_RS08 alu2)) ⊗
 (eq_w16 (pc_mask_RS08 alu1) (pc_mask_RS08 alu2)) ⊗
 (eq_w16 (spc_reg_RS08 alu1) (spc_reg_RS08 alu2)) ⊗
 (eq_b8 (x_map_RS08 alu1) (x_map_RS08 alu2)) ⊗
 (eq_b8 (ps_map_RS08 alu1) (ps_map_RS08 alu2)) ⊗
 (eq_bool (z_flag_RS08 alu1) (z_flag_RS08 alu2)) ⊗
 (eq_bool (c_flag_RS08 alu1) (c_flag_RS08 alu2)).
