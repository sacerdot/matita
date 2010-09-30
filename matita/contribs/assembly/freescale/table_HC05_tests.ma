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

include "freescale/table_HC05.ma".

(* HC05: opcode non implementati come da manuale *)
definition HC05_not_impl_byte ≝
 [〈x3,x1〉;〈x3,x2〉;〈x3,x5〉;〈x3,xB〉;〈x3,xE〉
 ;〈x4,x1〉;〈x4,x5〉;〈x4,xB〉;〈x4,xE〉
 ;〈x5,x1〉;〈x5,x2〉;〈x5,x5〉;〈x5,xB〉;〈x5,xE〉
 ;〈x6,x1〉;〈x6,x2〉;〈x6,x5〉;〈x6,xB〉;〈x6,xE〉
 ;〈x7,x1〉;〈x7,x2〉;〈x7,x5〉;〈x7,xB〉;〈x7,xE〉
 ;〈x8,x2〉;〈x8,x4〉;〈x8,x5〉;〈x8,x6〉;〈x8,x7〉;〈x8,x8〉;〈x8,x9〉;〈x8,xA〉;〈x8,xB〉;〈x8,xC〉;〈x8,xD〉
 ;〈x9,x0〉;〈x9,x1〉;〈x9,x2〉;〈x9,x3〉;〈x9,x4〉;〈x9,x5〉;〈x9,x6〉;〈x9,xE〉
 ;〈xA,x7〉;〈xA,xC〉;〈xA,xF〉
 ].

lemma ok_byte_table_HC05 : forall_byte8 (λb.
 (test_not_impl_byte b HC05_not_impl_byte     ⊙ eqb (get_byte_count HC05 b 0 opcode_table_HC05) 1) ⊗
 (⊖ (test_not_impl_byte b HC05_not_impl_byte) ⊙ eqb (get_byte_count HC05 b 0 opcode_table_HC05) 0))
 = true.
 reflexivity.
qed.

(* HC05: pseudocodici non implementati come da manuale *)
definition HC05_not_impl_pseudo ≝
 [ AIS ; AIX ; BGE ; BGND ; BGT ; BLE ; BLT ; CBEQA ; CBEQX ; CPHX ; DAA
 ; DBNZ ; DIV ; LDHX ; MOV ; NSA ; PSHA ; PSHH ; PSHX ; PULA ; PULH ; PULX
 ; SHA ; SLA ; STHX ; TAP ; TPA ; TSX ; TXS ].

lemma ok_pseudo_table_HC05 : forall_opcode (λo.
 (test_not_impl_pseudo o HC05_not_impl_pseudo     ⊙ leb 1 (get_pseudo_count HC05 o 0 opcode_table_HC05)) ⊗
 (⊖ (test_not_impl_pseudo o HC05_not_impl_pseudo) ⊙ eqb (get_pseudo_count HC05 o 0 opcode_table_HC05) 0))
 = true.
 reflexivity.
qed.

(* HC05: modalita' non implementate come da manuale *)
definition HC05_not_impl_mode ≝
 [ MODE_INHH ; MODE_SP1 ; MODE_SP2 ; MODE_DIR1_to_DIR1
 ; MODE_IMM1_to_DIR1 ; MODE_IX0p_to_DIR1 ; MODE_DIR1_to_IX0p
 ; MODE_INHA_and_IMM1 ; MODE_INHX_and_IMM1 ; MODE_IMM1_and_IMM1
 ; MODE_DIR1_and_IMM1 ; MODE_IX0_and_IMM1 ; MODE_IX0p_and_IMM1
 ; MODE_IX1_and_IMM1 ; MODE_IX1p_and_IMM1 ; MODE_SP1_and_IMM1
 ; MODE_TNY x0 ; MODE_TNY x1 ; MODE_TNY x2 ; MODE_TNY x3
 ; MODE_TNY x4 ; MODE_TNY x5 ; MODE_TNY x6 ; MODE_TNY x7
 ; MODE_TNY x8 ; MODE_TNY x9 ; MODE_TNY xA ; MODE_TNY xB
 ; MODE_TNY xC ; MODE_TNY xD ; MODE_TNY xE ; MODE_TNY xF
 ; MODE_SRT t00 ; MODE_SRT t01 ; MODE_SRT t02 ; MODE_SRT t03
 ; MODE_SRT t04 ; MODE_SRT t05 ; MODE_SRT t06 ; MODE_SRT t07
 ; MODE_SRT t08 ; MODE_SRT t09 ; MODE_SRT t0A ; MODE_SRT t0B
 ; MODE_SRT t0C ; MODE_SRT t0D ; MODE_SRT t0E ; MODE_SRT t0F
 ; MODE_SRT t10 ; MODE_SRT t11 ; MODE_SRT t12 ; MODE_SRT t13
 ; MODE_SRT t14 ; MODE_SRT t15 ; MODE_SRT t16 ; MODE_SRT t17
 ; MODE_SRT t18 ; MODE_SRT t19 ; MODE_SRT t1A ; MODE_SRT t1B
 ; MODE_SRT t1C ; MODE_SRT t1D ; MODE_SRT t1E ; MODE_SRT t1F ].

lemma ok_mode_table_HC05 : forall_instr_mode (λi.
 (test_not_impl_mode i HC05_not_impl_mode     ⊙ leb 1 (get_mode_count HC05 i 0 opcode_table_HC05)) ⊗
 (⊖ (test_not_impl_mode i HC05_not_impl_mode) ⊙ eqb (get_mode_count HC05 i 0 opcode_table_HC05) 0))
 = true.
 reflexivity.
qed.

lemma ok_OpIm_table_HC05 :
 forall_instr_mode (λi:instr_mode.
 forall_opcode     (λop:opcode.
  leb (get_OpIm_count HC05 (anyOP HC05 op) i 0 opcode_table_HC05) 1)) = true.
 reflexivity.
qed.
