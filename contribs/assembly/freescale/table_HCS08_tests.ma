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

include "freescale/table_HCS08.ma".

(* HCS08: opcode non implementati come da manuale (byte) *)
definition HCS08_not_impl_byte ≝
 [〈x8,xD〉
 ;〈x9,xE〉
 ;〈xA,xC〉
 ].

lemma ok_byte_table_HCS08 : forall_byte8 (λb.
 (test_not_impl_byte b HCS08_not_impl_byte     ⊙ eqb (get_byte_count HCS08 b 0 opcode_table_HCS08) 1) ⊗
 (⊖ (test_not_impl_byte b HCS08_not_impl_byte) ⊙ eqb (get_byte_count HCS08 b 0 opcode_table_HCS08) 0))
 = true.
 reflexivity.
qed.

(* HCS08: opcode non implementati come da manuale (0x9E+byte) *)
definition HCS08_not_impl_word ≝
 [〈x0,x0〉;〈x0,x1〉;〈x0,x2〉;〈x0,x3〉;〈x0,x4〉;〈x0,x5〉;〈x0,x6〉;〈x0,x7〉
 ;〈x0,x8〉;〈x0,x9〉;〈x0,xA〉;〈x0,xB〉;〈x0,xC〉;〈x0,xD〉;〈x0,xE〉;〈x0,xF〉
 ;〈x1,x0〉;〈x1,x1〉;〈x1,x2〉;〈x1,x3〉;〈x1,x4〉;〈x1,x5〉;〈x1,x6〉;〈x1,x7〉
 ;〈x1,x8〉;〈x1,x9〉;〈x1,xA〉;〈x1,xB〉;〈x1,xC〉;〈x1,xD〉;〈x1,xE〉;〈x1,xF〉
 ;〈x2,x0〉;〈x2,x1〉;〈x2,x2〉;〈x2,x3〉;〈x2,x4〉;〈x2,x5〉;〈x2,x6〉;〈x2,x7〉
 ;〈x2,x8〉;〈x2,x9〉;〈x2,xA〉;〈x2,xB〉;〈x2,xC〉;〈x2,xD〉;〈x2,xE〉;〈x2,xF〉
 ;〈x3,x0〉;〈x3,x1〉;〈x3,x2〉;〈x3,x3〉;〈x3,x4〉;〈x3,x5〉;〈x3,x6〉;〈x3,x7〉
 ;〈x3,x8〉;〈x3,x9〉;〈x3,xA〉;〈x3,xB〉;〈x3,xC〉;〈x3,xD〉;〈x3,xE〉;〈x3,xF〉
 ;〈x4,x0〉;〈x4,x1〉;〈x4,x2〉;〈x4,x3〉;〈x4,x4〉;〈x4,x5〉;〈x4,x6〉;〈x4,x7〉
 ;〈x4,x8〉;〈x4,x9〉;〈x4,xA〉;〈x4,xB〉;〈x4,xC〉;〈x4,xD〉;〈x4,xE〉;〈x4,xF〉
 ;〈x5,x0〉;〈x5,x1〉;〈x5,x2〉;〈x5,x3〉;〈x5,x4〉;〈x5,x5〉;〈x5,x6〉;〈x5,x7〉
 ;〈x5,x8〉;〈x5,x9〉;〈x5,xA〉;〈x5,xB〉;〈x5,xC〉;〈x5,xD〉;〈x5,xE〉;〈x5,xF〉
 ;〈x6,x2〉;〈x6,x5〉;〈x6,xE〉
 ;〈x7,x0〉;〈x7,x1〉;〈x7,x2〉;〈x7,x3〉;〈x7,x4〉;〈x7,x5〉;〈x7,x6〉;〈x7,x7〉
 ;〈x7,x8〉;〈x7,x9〉;〈x7,xA〉;〈x7,xB〉;〈x7,xC〉;〈x7,xD〉;〈x7,xE〉;〈x7,xF〉
 ;〈x8,x0〉;〈x8,x1〉;〈x8,x2〉;〈x8,x3〉;〈x8,x4〉;〈x8,x5〉;〈x8,x6〉;〈x8,x7〉
 ;〈x8,x8〉;〈x8,x9〉;〈x8,xA〉;〈x8,xB〉;〈x8,xC〉;〈x8,xD〉;〈x8,xE〉;〈x8,xF〉
 ;〈x9,x0〉;〈x9,x1〉;〈x9,x2〉;〈x9,x3〉;〈x9,x4〉;〈x9,x5〉;〈x9,x6〉;〈x9,x7〉
 ;〈x9,x8〉;〈x9,x9〉;〈x9,xA〉;〈x9,xB〉;〈x9,xC〉;〈x9,xD〉;〈x9,xE〉;〈x9,xF〉
 ;〈xA,x0〉;〈xA,x1〉;〈xA,x2〉;〈xA,x3〉;〈xA,x4〉;〈xA,x5〉;〈xA,x6〉;〈xA,x7〉;〈xA,x8〉;〈xA,x9〉;〈xA,xA〉;〈xA,xB〉;〈xA,xC〉;〈xA,xD〉;〈xA,xF〉
 ;〈xB,x0〉;〈xB,x1〉;〈xB,x2〉;〈xB,x3〉;〈xB,x4〉;〈xB,x5〉;〈xB,x6〉;〈xB,x7〉;〈xB,x8〉;〈xB,x9〉;〈xB,xA〉;〈xB,xB〉;〈xB,xC〉;〈xB,xD〉;〈xB,xF〉
 ;〈xC,x0〉;〈xC,x1〉;〈xC,x2〉;〈xC,x3〉;〈xC,x4〉;〈xC,x5〉;〈xC,x6〉;〈xC,x7〉;〈xC,x8〉;〈xC,x9〉;〈xC,xA〉;〈xC,xB〉;〈xC,xC〉;〈xC,xD〉;〈xC,xF〉
 ;〈xD,xC〉;〈xD,xD〉
 ;〈xE,xC〉;〈xE,xD〉
 ;〈xF,x0〉;〈xF,x1〉;〈xF,x2〉;〈xF,x4〉;〈xF,x5〉;〈xF,x6〉;〈xF,x7〉;〈xF,x8〉;〈xF,x9〉;〈xF,xA〉;〈xF,xB〉;〈xF,xC〉;〈xF,xD〉
 ].

lemma ok_word_table_HCS08 : forall_byte8 (λb.
 (test_not_impl_byte b HCS08_not_impl_word     ⊙ eqb (get_word_count HCS08 b 0 opcode_table_HCS08) 1) ⊗
 (⊖ (test_not_impl_byte b HCS08_not_impl_word) ⊙ eqb (get_word_count HCS08 b 0 opcode_table_HCS08) 0))
 = true.
 reflexivity.
qed.

(* HCS08: pseudocodici non implementati come da manuale *)
definition HCS08_not_impl_pseudo ≝
 [ SHA ; SLA ].

lemma ok_pseudo_table_HCS08 : forall_opcode (λo.
 (test_not_impl_pseudo o HCS08_not_impl_pseudo     ⊙ leb 1 (get_pseudo_count HCS08 o 0 opcode_table_HCS08)) ⊗
 (⊖ (test_not_impl_pseudo o HCS08_not_impl_pseudo) ⊙ eqb (get_pseudo_count HCS08 o 0 opcode_table_HCS08) 0))
 = true.
 reflexivity.
qed.

(* HCS08: modalita' non implementate come da manuale *)
definition HCS08_not_impl_mode ≝
 [ MODE_TNY x0 ; MODE_TNY x1 ; MODE_TNY x2 ; MODE_TNY x3
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

lemma ok_mode_table_HCS08 : forall_instr_mode (λi.
 (test_not_impl_mode i HCS08_not_impl_mode     ⊙ leb 1 (get_mode_count HCS08 i 0 opcode_table_HCS08)) ⊗
 (⊖ (test_not_impl_mode i HCS08_not_impl_mode) ⊙ eqb (get_mode_count HCS08 i 0 opcode_table_HCS08) 0))
 = true.
 reflexivity.
qed.

lemma ok_OpIm_table_HCS08 :
 forall_instr_mode (λi:instr_mode.
 forall_opcode     (λop:opcode.
  leb (get_OpIm_count HCS08 (anyOP HCS08 op) i 0 opcode_table_HCS08) 1)) = true.
 reflexivity.
qed.
