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
include "emulator/opcodes/IP2022_table.ma".

(* ******************* *)
(* TABELLA DELL'IP2022 *)
(* ******************* *)

(* IP2022: opcode non implementati come da manuale (byte) *)
ndefinition IP2022_not_impl_byte ≝
 [〈x0,x0〉;〈x5,x2〉;〈x5,x3〉;〈x5,x6〉;〈x5,x7〉;〈x6,x0〉;〈x6,x1〉;〈x6,x2〉
 ;〈x6,x3〉;〈x6,x4〉;〈x6,x5〉;〈x6,x6〉;〈x6,x7〉;〈x6,x8〉;〈x6,x9〉;〈x6,xA〉
 ;〈x6,xB〉;〈x6,xC〉;〈x6,xD〉;〈x6,xE〉;〈x6,xF〉;〈x7,x5〉 ].

(*nlemma ok_byte_table_IP2022 : forallc ? (λb.
 (test_not_impl_byte b IP2022_not_impl_byte     ⊙ eqc ? (get_byte_count IP2022 b 〈〈x0,x0〉:〈x0,x0〉〉 opcode_table_IP2022) 〈〈x0,x0〉:〈x0,x1〉〉) ⊗
 (⊖ (test_not_impl_byte b IP2022_not_impl_byte) ⊙ eqc ? (get_byte_count IP2022 b 〈〈x0,x0〉:〈x0,x0〉〉 opcode_table_IP2022) 〈〈x0,x0〉:〈x0,x0〉〉))
 = true.
 napply refl_eq.
nqed.*)

(* IP2022: opcode non implementati come da manuale (0x00+byte) *)
ndefinition IP2022_not_impl_word ≝
 [〈x1,xE〉;〈x1,xF〉
 ;〈x2,x0〉;〈x2,x1〉;〈x2,x2〉;〈x2,x3〉;〈x2,x4〉;〈x2,x5〉;〈x2,x6〉;〈x2,x7〉
 ;〈x2,x8〉;〈x2,x9〉;〈x2,xA〉;〈x2,xB〉;〈x2,xC〉;〈x2,xD〉;〈x2,xE〉;〈x2,xF〉
 ;〈x3,x0〉;〈x3,x1〉;〈x3,x2〉;〈x3,x3〉;〈x3,x4〉;〈x3,x5〉;〈x3,x6〉;〈x3,x7〉
 ;〈x3,x8〉;〈x3,x9〉;〈x3,xA〉;〈x3,xB〉;〈x3,xC〉;〈x3,xD〉;〈x3,xE〉;〈x3,xF〉
 ;〈x4,x0〉;〈x4,x1〉;〈x4,x2〉;〈x4,x3〉;〈x4,x4〉;〈x4,x5〉;〈x4,x6〉;〈x4,x7〉
 ;〈x4,x8〉;〈x4,x9〉;〈x4,xA〉;〈x4,xB〉;〈x4,xC〉;〈x4,xD〉;〈x4,xE〉;〈x4,xF〉
 ;〈x5,x0〉;〈x5,x1〉;〈x5,x2〉;〈x5,x3〉;〈x5,x4〉;〈x5,x5〉;〈x5,x6〉;〈x5,x7〉
 ;〈x5,x8〉;〈x5,x9〉;〈x5,xA〉;〈x5,xB〉;〈x5,xC〉;〈x5,xD〉;〈x5,xE〉;〈x5,xF〉
 ;〈x6,x0〉;〈x6,x1〉;〈x6,x2〉;〈x6,x3〉;〈x6,x4〉;〈x6,x5〉;〈x6,x6〉;〈x6,x7〉
 ;〈x6,x8〉;〈x6,x9〉;〈x6,xA〉;〈x6,xB〉;〈x6,xC〉;〈x6,xD〉;〈x6,xE〉;〈x6,xF〉
 ;〈x7,x0〉;〈x7,x1〉;〈x7,x2〉;〈x7,x3〉;〈x7,x4〉;〈x7,x5〉;〈x7,x6〉;〈x7,x7〉
 ;〈x7,x8〉;〈x7,x9〉;〈x7,xA〉;〈x7,xB〉;〈x7,xC〉;〈x7,xD〉;〈x7,xE〉;〈x7,xF〉
 ;〈x8,x0〉;〈x8,x1〉;〈x8,x2〉;〈x8,x3〉;〈x8,x4〉;〈x8,x5〉;〈x8,x6〉;〈x8,x7〉
 ;〈x8,x8〉;〈x8,x9〉;〈x8,xA〉;〈x8,xB〉;〈x8,xC〉;〈x8,xD〉;〈x8,xE〉;〈x8,xF〉
 ;〈x9,x0〉;〈x9,x1〉;〈x9,x2〉;〈x9,x3〉;〈x9,x4〉;〈x9,x5〉;〈x9,x6〉;〈x9,x7〉
 ;〈x9,x8〉;〈x9,x9〉;〈x9,xA〉;〈x9,xB〉;〈x9,xC〉;〈x9,xD〉;〈x9,xE〉;〈x9,xF〉
 ;〈xA,x0〉;〈xA,x1〉;〈xA,x2〉;〈xA,x3〉;〈xA,x4〉;〈xA,x5〉;〈xA,x6〉;〈xA,x7〉
 ;〈xA,x8〉;〈xA,x9〉;〈xA,xA〉;〈xA,xB〉;〈xA,xC〉;〈xA,xD〉;〈xA,xE〉;〈xA,xF〉
 ;〈xB,x0〉;〈xB,x1〉;〈xB,x2〉;〈xB,x3〉;〈xB,x4〉;〈xB,x5〉;〈xB,x6〉;〈xB,x7〉
 ;〈xB,x8〉;〈xB,x9〉;〈xB,xA〉;〈xB,xB〉;〈xB,xC〉;〈xB,xD〉;〈xB,xE〉;〈xB,xF〉
 ;〈xC,x0〉;〈xC,x1〉;〈xC,x2〉;〈xC,x3〉;〈xC,x4〉;〈xC,x5〉;〈xC,x6〉;〈xC,x7〉
 ;〈xC,x8〉;〈xC,x9〉;〈xC,xA〉;〈xC,xB〉;〈xC,xC〉;〈xC,xD〉;〈xC,xE〉;〈xC,xF〉
 ;〈xD,x0〉;〈xD,x1〉;〈xD,x2〉;〈xD,x3〉;〈xD,x4〉;〈xD,x5〉;〈xD,x6〉;〈xD,x7〉
 ;〈xD,x8〉;〈xD,x9〉;〈xD,xA〉;〈xD,xB〉;〈xD,xC〉;〈xD,xD〉;〈xD,xE〉;〈xD,xF〉
 ;〈xE,x0〉;〈xE,x1〉;〈xE,x2〉;〈xE,x3〉;〈xE,x4〉;〈xE,x5〉;〈xE,x6〉;〈xE,x7〉
 ;〈xE,x8〉;〈xE,x9〉;〈xE,xA〉;〈xE,xB〉;〈xE,xC〉;〈xE,xD〉;〈xE,xE〉;〈xE,xF〉
 ;〈xF,x0〉;〈xF,x1〉;〈xF,x2〉;〈xF,x3〉;〈xF,x4〉;〈xF,x5〉;〈xF,x6〉;〈xF,x7〉
 ;〈xF,x8〉;〈xF,x9〉;〈xF,xA〉;〈xF,xB〉;〈xF,xC〉;〈xF,xD〉;〈xF,xE〉;〈xF,xF〉
 ].

nlemma ok_word_table_IP2022 : forallc ? (λb.
 (test_not_impl_byte b IP2022_not_impl_word     ⊙ eqc ? (get_word_count IP2022 〈〈x0,x0〉:b〉 〈〈x0,x0〉:〈x0,x0〉〉 opcode_table_IP2022) 〈〈x0,x0〉:〈x0,x1〉〉) ⊗
 (⊖ (test_not_impl_byte b IP2022_not_impl_word) ⊙ eqc ? (get_word_count IP2022 〈〈x0,x0〉:b〉 〈〈x0,x0〉:〈x0,x0〉〉 opcode_table_IP2022) 〈〈x0,x0〉:〈x0,x0〉〉))
 = true.
 napply refl_eq.
nqed.

(* tutti gli pseudo implementati *)
nlemma ok_pseudo_table_IP2022 :
 forallc ? (λo.
  lec ? 〈〈x0,x0〉:〈x0,x1〉〉 (get_pseudo_count IP2022 o 〈〈x0,x0〉:〈x0,x0〉〉 opcode_table_IP2022)) = true.
 napply refl_eq.
nqed.

(* tutte le modalita' implementate *)
nlemma ok_mode_table_IP2022 :
 forallc ? (λi.
  lec ? 〈〈x0,x0〉:〈x0,x1〉〉 (get_mode_count IP2022 i 〈〈x0,x0〉:〈x0,x0〉〉 opcode_table_IP2022)) = true.
 napply refl_eq.
nqed.

nlemma ok_PsIm_table_IP2022 :
 forallc ? (λi.
 forallc ? (λps.
  lec ? (get_PsIm_count IP2022 ps i 〈〈x0,x0〉:〈x0,x0〉〉 opcode_table_IP2022) 〈〈x0,x0〉:〈x0,x1〉〉)) = true.
 napply refl_eq.
nqed.
