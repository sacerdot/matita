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

include "emulator/opcodes/pseudo.ma".
include "emulator/opcodes/RS08_table.ma".

(* ***************** *)
(* TABELLA DELL'RS08 *)
(* ***************** *)

(* RS08: opcode non implementati come da manuale *)
ndefinition RS08_not_impl_byte ≝
 [〈x3,x2〉;〈x3,x3〉;〈x3,xD〉
 ;〈x4,x0〉;〈x4,x7〉;〈x4,xD〉
 ;〈xA,x3〉;〈xA,x5〉;〈xA,x7〉
 ;〈xB,x3〉;〈xB,x5〉
 ].

nlemma ok_byte_table_RS08 : forall_b8 (λb.
 (test_not_impl_byte b RS08_not_impl_byte     ⊙ eq_w16 (get_byte_count RS08 b 〈〈x0,x0〉:〈x0,x0〉〉 opcode_table_RS08) 〈〈x0,x0〉:〈x0,x1〉〉) ⊗
 (⊖ (test_not_impl_byte b RS08_not_impl_byte) ⊙ eq_w16 (get_byte_count RS08 b 〈〈x0,x0〉:〈x0,x0〉〉 opcode_table_RS08) 〈〈x0,x0〉:〈x0,x0〉〉))
 = true.
 napply refl_eq.
nqed.

(* RS08: pseudocodici non implementati come da manuale *)
ndefinition RS08_not_impl_pseudo ≝
 [ AIS ; AIX ; ASR ; BGE ; BGT ; BHCC ; BHCS ; BHI ; BIH ; BIL ; BIT ; BLE ; BLS
 ; BLT ; BMC ; BMI ; BMS ; BPL ; BRN ; CBEQX ; CLI ; CPHX ; CPX ; DAA ; DIV
 ; LDHX ; LDX ; MUL ; NEG ; NSA ; PSHA ; PSHH ; PSHX ; PULA ; PULH ; PULX ; RSP  
 ; RTI ; SEI ; STHX ; STX ; SWI ; TAP ; TAX ; TPA ; TST ; TSX ; TXA ; TXS ].

nlemma ok_pseudo_table_RS08 : forall_Freescale_pseudo (λo.
 (test_not_impl_pseudo RS08 o RS08_not_impl_pseudo     ⊙ le_w16 〈〈x0,x0〉:〈x0,x1〉〉 (get_pseudo_count RS08 o 〈〈x0,x0〉:〈x0,x0〉〉 opcode_table_RS08)) ⊗
 (⊖ (test_not_impl_pseudo RS08 o RS08_not_impl_pseudo) ⊙ eq_w16 (get_pseudo_count RS08 o 〈〈x0,x0〉:〈x0,x0〉〉 opcode_table_RS08) 〈〈x0,x0〉:〈x0,x0〉〉))
 = true.
 napply refl_eq.
nqed.

(* RS08: modalita' non implementate come da manuale *)
ndefinition RS08_not_impl_mode ≝
 [ MODE_INHX ; MODE_INHH ; MODE_INHX0ADD ; MODE_INHX1ADD ; MODE_INHX2ADD ; MODE_IMM1EXT
 ; MODE_DIR2 ; MODE_IX0 ; MODE_IX1 ; MODE_IX2 ; MODE_SP1 ; MODE_SP2
 ; MODE_IX0p_to_DIR1 ; MODE_DIR1_to_IX0p ; MODE_INHX_and_IMM1 ; MODE_IX0_and_IMM1
 ; MODE_IX0p_and_IMM1 ; MODE_IX1_and_IMM1 ; MODE_IX1p_and_IMM1 ; MODE_SP1_and_IMM1 ].

nlemma ok_mode_table_RS08 : forall_Freescale_im (λi.
 (test_not_impl_mode RS08 i RS08_not_impl_mode     ⊙ le_w16 〈〈x0,x0〉:〈x0,x1〉〉 (get_mode_count RS08 i 〈〈x0,x0〉:〈x0,x0〉〉 opcode_table_RS08)) ⊗
 (⊖ (test_not_impl_mode RS08 i RS08_not_impl_mode) ⊙ eq_w16 (get_mode_count RS08 i 〈〈x0,x0〉:〈x0,x0〉〉 opcode_table_RS08) 〈〈x0,x0〉:〈x0,x0〉〉))
 = true.
 napply refl_eq.
nqed.

nlemma ok_PsIm_table_RS08 :
 forall_Freescale_im (λi:Freescale_instr_mode.
 forall_Freescale_pseudo (λps:Freescale_pseudo.
  le_w16 (get_PsIm_count RS08 ps i 〈〈x0,x0〉:〈x0,x0〉〉 opcode_table_RS08) 〈〈x0,x0〉:〈x0,x1〉〉)) = true.
 napply refl_eq.
nqed.
