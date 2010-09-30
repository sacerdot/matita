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

(* ALU dell'HC08/HCS08 *) 
nrecord alu_HC08: Type ≝
 {
 (* A: registo accumulatore *)
 acc_low_reg_HC08 : byte8;
 (* X: registro indice parte bassa *)
 indX_low_reg_HC08 : byte8;
 (* H: registro indice parte alta *)
 indX_high_reg_HC08 : byte8;
 (* SP: registo stack pointer *)
 sp_reg_HC08 : word16;
 (* PC: registro program counter *)
 pc_reg_HC08 : word16;
 
 (* V: flag overflow *)
 v_flag_HC08 : bool;
 (* H: flag semi-carry (somma nibble basso) *)
 h_flag_HC08 : bool;
 (* I: flag mascheramento degli interrupt mascherabili: 1=mascherati *)
 i_flag_HC08 : bool;
 (* N: flag segno/negativita' *)
 n_flag_HC08 : bool;
 (* Z: flag zero *)
 z_flag_HC08 : bool;
 (* C: flag carry *)
 c_flag_HC08 : bool;
 
 (* IRQ: flag che simula il pin esterno IRQ *)
 irq_flag_HC08 : bool
 }.

notation "{hvbox('A_Reg' ≝ acclow ; break 'X_Reg' ≝ indxlow ; break 'H_Reg' ≝ indxhigh ; break 'Sp_Reg' ≝ sp ; break 'Pc_Reg' ≝ pc ; break 'V_Flag' ≝ vfl ; break 'H_Flag' ≝ hfl ; break 'I_Flag' ≝ ifl ; break 'N_Flag' ≝ nfl ; break 'Z_Flag' ≝ zfl ; break 'C_Flag' ≝ cfl ; break 'IRQ_Flag' ≝ irqfl)}"
 non associative with precedence 80 for
 @{ 'mk_alu_HC08 $acclow $indxlow $indxhigh $sp $pc $vfl $hfl $ifl $nfl $zfl $cfl $irqfl }.
interpretation "mk_alu_HC08" 'mk_alu_HC08 acclow indxlow indxhigh sp pc vfl hfl ifl nfl zfl cfl irqfl =
 (mk_alu_HC08 acclow indxlow indxhigh sp pc vfl hfl ifl nfl zfl cfl irqfl).

(* ****** *)
(* SETTER *)
(* ****** *)

(* setter specifico HC08/HCS08 di A *)
ndefinition set_acc_8_low_reg_HC08 ≝
λalu.λacclow':byte8.
 mk_alu_HC08
  acclow'
  (indX_low_reg_HC08 alu)
  (indX_high_reg_HC08 alu)
  (sp_reg_HC08 alu)
  (pc_reg_HC08 alu)
  (v_flag_HC08 alu)
  (h_flag_HC08 alu)
  (i_flag_HC08 alu)
  (n_flag_HC08 alu)
  (z_flag_HC08 alu)
  (c_flag_HC08 alu)
  (irq_flag_HC08 alu).

(* setter specifico HC08/HCS08 di X *)
ndefinition set_indX_8_low_reg_HC08 ≝
λalu.λindxlow':byte8.
 mk_alu_HC08
  (acc_low_reg_HC08 alu)
  indxlow'
  (indX_high_reg_HC08 alu)
  (sp_reg_HC08 alu)
  (pc_reg_HC08 alu)
  (v_flag_HC08 alu)
  (h_flag_HC08 alu)
  (i_flag_HC08 alu)
  (n_flag_HC08 alu)
  (z_flag_HC08 alu)
  (c_flag_HC08 alu)
  (irq_flag_HC08 alu).

(* setter specifico HC08/HCS08 di H *)
ndefinition set_indX_8_high_reg_HC08 ≝
λalu.λindxhigh':byte8.
 mk_alu_HC08
  (acc_low_reg_HC08 alu)
  (indX_low_reg_HC08 alu)
  indxhigh'
  (sp_reg_HC08 alu)
  (pc_reg_HC08 alu)
  (v_flag_HC08 alu)
  (h_flag_HC08 alu)
  (i_flag_HC08 alu)
  (n_flag_HC08 alu)
  (z_flag_HC08 alu)
  (c_flag_HC08 alu)
  (irq_flag_HC08 alu).

(* setter specifico HC08/HCS08 di H:X *)
ndefinition set_indX_16_reg_HC08 ≝
λalu.λindx16:word16.
 mk_alu_HC08
  (acc_low_reg_HC08 alu)
  (cnL ? indx16)
  (cnH ? indx16)
  (sp_reg_HC08 alu)
  (pc_reg_HC08 alu)
  (v_flag_HC08 alu)
  (h_flag_HC08 alu)
  (i_flag_HC08 alu)
  (n_flag_HC08 alu)
  (z_flag_HC08 alu)
  (c_flag_HC08 alu)
  (irq_flag_HC08 alu).

(* setter specifico HC08/HCS08 di SP *)
ndefinition set_sp_reg_HC08 ≝
λalu.λsp':word16.
 mk_alu_HC08
  (acc_low_reg_HC08 alu)
  (indX_low_reg_HC08 alu)
  (indX_high_reg_HC08 alu)
  sp'
  (pc_reg_HC08 alu)
  (v_flag_HC08 alu)
  (h_flag_HC08 alu)
  (i_flag_HC08 alu)
  (n_flag_HC08 alu)
  (z_flag_HC08 alu)
  (c_flag_HC08 alu)
  (irq_flag_HC08 alu).

(* setter specifico HC08/HCS08 di PC *)
ndefinition set_pc_reg_HC08 ≝
λalu.λpc':word16.
 mk_alu_HC08
  (acc_low_reg_HC08 alu)
  (indX_low_reg_HC08 alu)
  (indX_high_reg_HC08 alu)
  (sp_reg_HC08 alu)
  pc'
  (v_flag_HC08 alu)
  (h_flag_HC08 alu)
  (i_flag_HC08 alu)
  (n_flag_HC08 alu)
  (z_flag_HC08 alu)
  (c_flag_HC08 alu)
  (irq_flag_HC08 alu).

(* setter specifico HC08/HCS08 di V *)
ndefinition set_v_flag_HC08 ≝
λalu.λvfl':bool.
 mk_alu_HC08
  (acc_low_reg_HC08 alu)
  (indX_low_reg_HC08 alu)
  (indX_high_reg_HC08 alu)
  (sp_reg_HC08 alu)
  (pc_reg_HC08 alu)
  vfl'
  (h_flag_HC08 alu)
  (i_flag_HC08 alu)
  (n_flag_HC08 alu)
  (z_flag_HC08 alu)
  (c_flag_HC08 alu)
  (irq_flag_HC08 alu).

(* setter specifico HC08/HCS08 di H *)
ndefinition set_h_flag_HC08 ≝
λalu.λhfl':bool.
 mk_alu_HC08
  (acc_low_reg_HC08 alu)
  (indX_low_reg_HC08 alu)
  (indX_high_reg_HC08 alu)
  (sp_reg_HC08 alu)
  (pc_reg_HC08 alu)
  (v_flag_HC08 alu)
  hfl'
  (i_flag_HC08 alu)
  (n_flag_HC08 alu)
  (z_flag_HC08 alu)
  (c_flag_HC08 alu)
  (irq_flag_HC08 alu).

(* setter specifico HC08/HCS08 di I *)
ndefinition set_i_flag_HC08 ≝
λalu.λifl':bool.
 mk_alu_HC08
  (acc_low_reg_HC08 alu)
  (indX_low_reg_HC08 alu)
  (indX_high_reg_HC08 alu)
  (sp_reg_HC08 alu)
  (pc_reg_HC08 alu)
  (v_flag_HC08 alu)
  (h_flag_HC08 alu)
  ifl'
  (n_flag_HC08 alu)
  (z_flag_HC08 alu)
  (c_flag_HC08 alu)
  (irq_flag_HC08 alu).

(* setter specifico HC08/HCS08 di N *)
ndefinition set_n_flag_HC08 ≝
λalu.λnfl':bool.
 mk_alu_HC08
  (acc_low_reg_HC08 alu)
  (indX_low_reg_HC08 alu)
  (indX_high_reg_HC08 alu)
  (sp_reg_HC08 alu)
  (pc_reg_HC08 alu)
  (v_flag_HC08 alu)
  (h_flag_HC08 alu)
  (i_flag_HC08 alu)
  nfl'
  (z_flag_HC08 alu)
  (c_flag_HC08 alu)
  (irq_flag_HC08 alu).

(* setter specifico HC08/HCS08 di Z *)
ndefinition set_z_flag_HC08 ≝
λalu.λzfl':bool.
 mk_alu_HC08
  (acc_low_reg_HC08 alu)
  (indX_low_reg_HC08 alu)
  (indX_high_reg_HC08 alu)
  (sp_reg_HC08 alu)
  (pc_reg_HC08 alu)
  (v_flag_HC08 alu)
  (h_flag_HC08 alu)
  (i_flag_HC08 alu)
  (n_flag_HC08 alu)
  zfl'
  (c_flag_HC08 alu)
  (irq_flag_HC08 alu).

(* setter specifico HC08/HCS08 di C *)
ndefinition set_c_flag_HC08 ≝
λalu.λcfl':bool.
 mk_alu_HC08
  (acc_low_reg_HC08 alu)
  (indX_low_reg_HC08 alu)
  (indX_high_reg_HC08 alu)
  (sp_reg_HC08 alu)
  (pc_reg_HC08 alu)
  (v_flag_HC08 alu)
  (h_flag_HC08 alu)
  (i_flag_HC08 alu)
  (n_flag_HC08 alu)
  (z_flag_HC08 alu)
  cfl'
  (irq_flag_HC08 alu).

(* setter specifico HC08/HCS08 di IRQ *)
ndefinition set_irq_flag_HC08 ≝
λalu.λirqfl':bool.
 mk_alu_HC08
  (acc_low_reg_HC08 alu)
  (indX_low_reg_HC08 alu)
  (indX_high_reg_HC08 alu)
  (sp_reg_HC08 alu)
  (pc_reg_HC08 alu)
  (v_flag_HC08 alu)
  (h_flag_HC08 alu)
  (i_flag_HC08 alu)
  (n_flag_HC08 alu)
  (z_flag_HC08 alu)
  (c_flag_HC08 alu)
  irqfl'.

(* ***************** *)
(* CONFRONTO FRA ALU *)
(* ***************** *)

(* confronto registro per registro dell'HC08 *)
ndefinition eq_HC08_alu ≝
λalu1,alu2:alu_HC08.
 (eq_b8 (acc_low_reg_HC08 alu1) (acc_low_reg_HC08 alu2)) ⊗
 (eq_b8 (indX_low_reg_HC08 alu1) (indX_low_reg_HC08 alu2)) ⊗
 (eq_b8 (indX_high_reg_HC08 alu1) (indX_high_reg_HC08 alu2)) ⊗
 (eq_w16 (sp_reg_HC08 alu1) (sp_reg_HC08 alu2)) ⊗
 (eq_w16 (pc_reg_HC08 alu1) (pc_reg_HC08 alu2)) ⊗
 (eq_bool (v_flag_HC08 alu1) (v_flag_HC08 alu2)) ⊗
 (eq_bool (h_flag_HC08 alu1) (h_flag_HC08 alu2)) ⊗
 (eq_bool (i_flag_HC08 alu1) (i_flag_HC08 alu2)) ⊗
 (eq_bool (n_flag_HC08 alu1) (n_flag_HC08 alu2)) ⊗
 (eq_bool (z_flag_HC08 alu1) (z_flag_HC08 alu2)) ⊗
 (eq_bool (c_flag_HC08 alu1) (c_flag_HC08 alu2)) ⊗
 (eq_bool (irq_flag_HC08 alu1) (irq_flag_HC08 alu2)).
