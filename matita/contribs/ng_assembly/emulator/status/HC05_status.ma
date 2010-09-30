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

(* ALU dell'HC05 *)
nrecord alu_HC05: Type ≝
 {
 (* A: registo accumulatore *)
 acc_low_reg_HC05 : byte8;
 (* X: registro indice *)
 indX_low_reg_HC05 : byte8;
 (* SP: registo stack pointer *)
 sp_reg_HC05 : word16;
 (* modificatori di SP: per esempio e' definito come 0000000011xxxxxxb *)
 (* la logica della sua costruzione e' quindi (SP∧mask)∨fix *)
 (* totalmente racchiusa nella ALU, bastera' fare get(set(SP)) *)
 sp_mask_HC05 : word16;
 sp_fix_HC05 : word16;
 (* PC: registro program counter *)
 pc_reg_HC05 : word16;
 (* modificatore di PC: per esempio e' definito come 00xxxxxxxxxxxxxxb *)
 (* la logica della sua costruzione e' quindi (PC∧mask) *)
 (* totalmente racchiusa nella ALU, bastera' fare get(set(PC)) *)
 pc_mask_HC05 : word16;
 
 (* H: flag semi-carry (somma nibble basso) *)
 h_flag_HC05 : bool;
 (* I: flag mascheramento degli interrupt mascherabili: 1=mascherati *)
 i_flag_HC05 : bool;
 (* N: flag segno/negativita' *)
 n_flag_HC05 : bool;
 (* Z: flag zero *)
 z_flag_HC05 : bool;
 (* C: flag carry *)
 c_flag_HC05 : bool;
 
 (* IRQ: flag che simula il pin esterno IRQ *)
 irq_flag_HC05 : bool
 }.

notation "{hvbox('A_Reg' ≝ acclow ; break 'X_Reg' ≝ indxlow ; break 'Sp_Reg' ≝ sp ; break 'Sp_Mask' ≝ spm ; break 'Sp_Fix' ≝ spf ; break 'Pc_Reg' ≝ pc ; break 'Pc_Mask' ≝ pcm ; break 'H_Flag' ≝ hfl ; break 'I_Flag' ≝ ifl ; break 'N_Flag' ≝ nfl ; break 'Z_Flag' ≝ zfl ; break 'C_Flag' ≝ cfl ; break 'IRQ_Flag' ≝ irqfl)}"
 non associative with precedence 80 for
 @{ 'mk_alu_HC05 $acclow $indxlow $sp $spm $spf $pc $pcm $hfl $ifl $nfl $zfl $cfl $irqfl }.
interpretation "mk_alu_HC05" 'mk_alu_HC05 acclow indxlow sp spm spf pc pcm hfl ifl nfl zfl cfl irqfl =
 (mk_alu_HC05 acclow indxlow sp spm spf pc pcm hfl ifl nfl zfl cfl irqfl).

(* ****** *)
(* SETTER *)
(* ****** *)

(* setter specifico HC05 di A *)
ndefinition set_acc_8_low_reg_HC05 ≝
λalu.λacclow':byte8.
 mk_alu_HC05
  acclow'
  (indX_low_reg_HC05 alu)
  (sp_reg_HC05 alu)
  (sp_mask_HC05 alu)
  (sp_fix_HC05 alu)
  (pc_reg_HC05 alu)
  (pc_mask_HC05 alu)
  (h_flag_HC05 alu)
  (i_flag_HC05 alu)
  (n_flag_HC05 alu)
  (z_flag_HC05 alu)
  (c_flag_HC05 alu)
  (irq_flag_HC05 alu).

(* setter specifico HC05 di X *)
ndefinition set_indX_8_low_reg_HC05 ≝
λalu.λindxlow':byte8.
 mk_alu_HC05
  (acc_low_reg_HC05 alu)
  indxlow'
  (sp_reg_HC05 alu)
  (sp_mask_HC05 alu)
  (sp_fix_HC05 alu)
  (pc_reg_HC05 alu)
  (pc_mask_HC05 alu)
  (h_flag_HC05 alu)
  (i_flag_HC05 alu)
  (n_flag_HC05 alu)
  (z_flag_HC05 alu)
  (c_flag_HC05 alu)
  (irq_flag_HC05 alu).

(* setter specifico HC05 di SP, effettua (SP∧mask)∨fix *)
ndefinition set_sp_reg_HC05 ≝
λalu.λsp':word16.
 mk_alu_HC05
  (acc_low_reg_HC05 alu)
  (indX_low_reg_HC05 alu)
  (or_w16 (and_w16 sp' (sp_mask_HC05 alu)) (sp_fix_HC05 alu))
  (sp_mask_HC05 alu)
  (sp_fix_HC05 alu)
  (pc_reg_HC05 alu)
  (pc_mask_HC05 alu)
  (h_flag_HC05 alu)
  (i_flag_HC05 alu)
  (n_flag_HC05 alu)
  (z_flag_HC05 alu)
  (c_flag_HC05 alu)
  (irq_flag_HC05 alu).

(* setter specifico HC05 di PC, effettua PC∧mask *)
ndefinition set_pc_reg_HC05 ≝
λalu.λpc':word16.
 mk_alu_HC05
  (acc_low_reg_HC05 alu)
  (indX_low_reg_HC05 alu)
  (sp_reg_HC05 alu)
  (sp_mask_HC05 alu)
  (sp_fix_HC05 alu)
  (and_w16 pc' (pc_mask_HC05 alu))
  (pc_mask_HC05 alu)
  (h_flag_HC05 alu)
  (i_flag_HC05 alu)
  (n_flag_HC05 alu)
  (z_flag_HC05 alu)
  (c_flag_HC05 alu)
  (irq_flag_HC05 alu).

(* setter specifico HC05 di H *)
ndefinition set_h_flag_HC05 ≝
λalu.λhfl':bool.
 mk_alu_HC05
  (acc_low_reg_HC05 alu)
  (indX_low_reg_HC05 alu)
  (sp_reg_HC05 alu)
  (sp_mask_HC05 alu)
  (sp_fix_HC05 alu)
  (pc_reg_HC05 alu)
  (pc_mask_HC05 alu)
  hfl'
  (i_flag_HC05 alu)
  (n_flag_HC05 alu)
  (z_flag_HC05 alu)
  (c_flag_HC05 alu)
  (irq_flag_HC05 alu).

(* setter specifico HC05 di I *)
ndefinition set_i_flag_HC05 ≝
λalu.λifl':bool.
 mk_alu_HC05
  (acc_low_reg_HC05 alu)
  (indX_low_reg_HC05 alu)
  (sp_reg_HC05 alu)
  (sp_mask_HC05 alu)
  (sp_fix_HC05 alu)
  (pc_reg_HC05 alu)
  (pc_mask_HC05 alu)
  (h_flag_HC05 alu)
  ifl'
  (n_flag_HC05 alu)
  (z_flag_HC05 alu)
  (c_flag_HC05 alu)
  (irq_flag_HC05 alu).

(* setter specifico HC05 di N *)
ndefinition set_n_flag_HC05 ≝
λalu.λnfl':bool.
 mk_alu_HC05
  (acc_low_reg_HC05 alu)
  (indX_low_reg_HC05 alu)
  (sp_reg_HC05 alu)
  (sp_mask_HC05 alu)
  (sp_fix_HC05 alu)
  (pc_reg_HC05 alu)
  (pc_mask_HC05 alu)
  (h_flag_HC05 alu)
  (i_flag_HC05 alu)
  nfl'
  (z_flag_HC05 alu)
  (c_flag_HC05 alu)
  (irq_flag_HC05 alu).

(* setter specifico HC05 di Z *)
ndefinition set_z_flag_HC05 ≝
λalu.λzfl':bool.
 mk_alu_HC05
  (acc_low_reg_HC05 alu)
  (indX_low_reg_HC05 alu)
  (sp_reg_HC05 alu)
  (sp_mask_HC05 alu)
  (sp_fix_HC05 alu)
  (pc_reg_HC05 alu)
  (pc_mask_HC05 alu)
  (h_flag_HC05 alu)
  (i_flag_HC05 alu)
  (n_flag_HC05 alu)
  zfl'
  (c_flag_HC05 alu)
  (irq_flag_HC05 alu).

(* setter specifico HC05 di C *)
ndefinition set_c_flag_HC05 ≝
λalu.λcfl':bool.
 mk_alu_HC05
  (acc_low_reg_HC05 alu)
  (indX_low_reg_HC05 alu)
  (sp_reg_HC05 alu)
  (sp_mask_HC05 alu)
  (sp_fix_HC05 alu)
  (pc_reg_HC05 alu)
  (pc_mask_HC05 alu)
  (h_flag_HC05 alu)
  (i_flag_HC05 alu)
  (n_flag_HC05 alu)
  (z_flag_HC05 alu)
  cfl'
  (irq_flag_HC05 alu).

(* setter specifico HC05 di IRQ *)
ndefinition set_irq_flag_HC05 ≝
λalu.λirqfl':bool.
 mk_alu_HC05
  (acc_low_reg_HC05 alu)
  (indX_low_reg_HC05 alu)
  (sp_reg_HC05 alu)
  (sp_mask_HC05 alu)
  (sp_fix_HC05 alu)
  (pc_reg_HC05 alu)
  (pc_mask_HC05 alu)
  (h_flag_HC05 alu)
  (i_flag_HC05 alu)
  (n_flag_HC05 alu)
  (z_flag_HC05 alu)
  (c_flag_HC05 alu)
  irqfl'.

(* ***************** *)
(* CONFRONTO FRA ALU *)
(* ***************** *)

(* confronto registro per registro dell'HC05 *)
ndefinition eq_HC05_alu ≝
λalu1,alu2:alu_HC05.
 (eq_b8 (acc_low_reg_HC05 alu1) (acc_low_reg_HC05 alu2)) ⊗
 (eq_b8 (indX_low_reg_HC05 alu1) (indX_low_reg_HC05 alu2)) ⊗
 (eq_w16 (sp_reg_HC05 alu1) (sp_reg_HC05 alu2)) ⊗
 (eq_w16 (sp_mask_HC05 alu1) (sp_mask_HC05 alu2)) ⊗
 (eq_w16 (sp_fix_HC05 alu1) (sp_fix_HC05 alu2)) ⊗
 (eq_w16 (pc_reg_HC05 alu1) (pc_reg_HC05 alu2)) ⊗
 (eq_w16 (pc_mask_HC05 alu1) (pc_mask_HC05 alu2)) ⊗
 (eq_bool (h_flag_HC05 alu1) (h_flag_HC05 alu2)) ⊗
 (eq_bool (i_flag_HC05 alu1) (i_flag_HC05 alu2)) ⊗
 (eq_bool (n_flag_HC05 alu1) (n_flag_HC05 alu2)) ⊗
 (eq_bool (z_flag_HC05 alu1) (z_flag_HC05 alu2)) ⊗
 (eq_bool (c_flag_HC05 alu1) (c_flag_HC05 alu2)) ⊗
 (eq_bool (irq_flag_HC05 alu1) (irq_flag_HC05 alu2)).
