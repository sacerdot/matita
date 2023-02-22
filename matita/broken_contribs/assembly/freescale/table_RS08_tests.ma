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

include "freescale/table_RS08.ma".

(* RS08: opcode non implementati come da manuale *)
definition RS08_not_impl_byte ≝
 [〈x3,x2〉;〈x3,x3〉;〈x3,xD〉
 ;〈x4,x0〉;〈x4,x7〉;〈x4,xD〉
 ;〈xA,x3〉;〈xA,x5〉;〈xA,x7〉
 ;〈xB,x3〉;〈xB,x5〉
 ].

lemma ok_byte_table_RS08 : forall_byte8 (λb.
 (test_not_impl_byte b RS08_not_impl_byte     ⊙ eqb (get_byte_count RS08 b 0 opcode_table_RS08) 1) ⊗
 (⊖ (test_not_impl_byte b RS08_not_impl_byte) ⊙ eqb (get_byte_count RS08 b 0 opcode_table_RS08) 0))
 = true.
 reflexivity.
qed.

(* RS08: pseudocodici non implementati come da manuale *)
definition RS08_not_impl_pseudo ≝
 [ AIS ; AIX ; ASR ; BGE ; BGT ; BHCC ; BHCS ; BHI ; BIH ; BIL ; BIT ; BLE ; BLS
 ; BLT ; BMC ; BMI ; BMS ; BPL ; BRN ; CBEQX ; CLI ; CPHX ; CPX ; DAA ; DIV
 ; LDHX ; LDX ; MUL ; NEG ; NSA ; PSHA ; PSHH ; PSHX ; PULA ; PULH ; PULX ; RSP  
 ; RTI ; SEI ; STHX ; STX ; SWI ; TAP ; TAX ; TPA ; TST ; TSX ; TXA ; TXS ].

lemma ok_pseudo_table_RS08 : forall_opcode (λo.
 (test_not_impl_pseudo o RS08_not_impl_pseudo     ⊙ leb 1 (get_pseudo_count RS08 o 0 opcode_table_RS08)) ⊗
 (⊖ (test_not_impl_pseudo o RS08_not_impl_pseudo) ⊙ eqb (get_pseudo_count RS08 o 0 opcode_table_RS08) 0))
 = true.
 reflexivity.
qed.

(* RS08: modalita' non implementate come da manuale *)
definition RS08_not_impl_mode ≝
 [ MODE_INHX ; MODE_INHH ; MODE_INHX0ADD ; MODE_INHX1ADD ; MODE_INHX2ADD ; MODE_IMM1EXT
 ; MODE_DIR2 ; MODE_IX0 ; MODE_IX1 ; MODE_IX2 ; MODE_SP1 ; MODE_SP2
 ; MODE_IX0p_to_DIR1 ; MODE_DIR1_to_IX0p ; MODE_INHX_and_IMM1 ; MODE_IX0_and_IMM1
 ; MODE_IX0p_and_IMM1 ; MODE_IX1_and_IMM1 ; MODE_IX1p_and_IMM1 ; MODE_SP1_and_IMM1 ].

lemma ok_mode_table_RS08 : forall_instr_mode (λi.
 (test_not_impl_mode i RS08_not_impl_mode     ⊙ leb 1 (get_mode_count RS08 i 0 opcode_table_RS08)) ⊗
 (⊖ (test_not_impl_mode i RS08_not_impl_mode) ⊙ eqb (get_mode_count RS08 i 0 opcode_table_RS08) 0))
 = true.
 reflexivity.
qed.

lemma ok_OpIm_table_RS08 :
 forall_instr_mode (λi:instr_mode.
 forall_opcode     (λop:opcode.
  leb (get_OpIm_count RS08 (anyOP RS08 op) i 0 opcode_table_RS08) 1)) = true.
 reflexivity.
qed.
