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

include "freescale/word16.ma".

(* ************************ *)
(* DEFINIZIONE DEGLI OTTALI *)
(* ************************ *)

inductive oct : Type ≝
  o0: oct
| o1: oct
| o2: oct
| o3: oct
| o4: oct
| o5: oct
| o6: oct
| o7: oct.

(* ottali → esadecimali *)
definition exadecim_of_oct ≝
λo:oct.
 match o with
  [ o0 ⇒ x0 | o1 ⇒ x1 | o2 ⇒ x2 | o3 ⇒ x3
  | o4 ⇒ x4 | o5 ⇒ x5 | o6 ⇒ x6 | o7 ⇒ x7 ].

coercion exadecim_of_oct.

(* iteratore sugli ottali *)
definition forall_oct ≝ λP.
 P o0 ⊗ P o1 ⊗ P o2 ⊗ P o3 ⊗ P o4 ⊗ P o5 ⊗ P o6 ⊗ P o7.

(* ***************************** *)
(* DEFINIZIONE DEI BITRIGESIMALI *)
(* ***************************** *)

inductive bitrigesim : Type ≝
  t00: bitrigesim
| t01: bitrigesim
| t02: bitrigesim
| t03: bitrigesim
| t04: bitrigesim
| t05: bitrigesim
| t06: bitrigesim
| t07: bitrigesim
| t08: bitrigesim
| t09: bitrigesim
| t0A: bitrigesim
| t0B: bitrigesim
| t0C: bitrigesim
| t0D: bitrigesim
| t0E: bitrigesim
| t0F: bitrigesim
| t10: bitrigesim
| t11: bitrigesim
| t12: bitrigesim
| t13: bitrigesim
| t14: bitrigesim
| t15: bitrigesim
| t16: bitrigesim
| t17: bitrigesim
| t18: bitrigesim
| t19: bitrigesim
| t1A: bitrigesim
| t1B: bitrigesim
| t1C: bitrigesim
| t1D: bitrigesim
| t1E: bitrigesim
| t1F: bitrigesim.

(* bitrigesimali → byte *)
definition byte8_of_bitrigesim ≝
λt:bitrigesim.
 match t with
  [ t00 ⇒ 〈x0,x0〉 | t01 ⇒ 〈x0,x1〉 | t02 ⇒ 〈x0,x2〉 | t03 ⇒ 〈x0,x3〉
  | t04 ⇒ 〈x0,x4〉 | t05 ⇒ 〈x0,x5〉 | t06 ⇒ 〈x0,x6〉 | t07 ⇒ 〈x0,x7〉
  | t08 ⇒ 〈x0,x8〉 | t09 ⇒ 〈x0,x9〉 | t0A ⇒ 〈x0,xA〉 | t0B ⇒ 〈x0,xB〉
  | t0C ⇒ 〈x0,xC〉 | t0D ⇒ 〈x0,xD〉 | t0E ⇒ 〈x0,xE〉 | t0F ⇒ 〈x0,xF〉
  | t10 ⇒ 〈x1,x0〉 | t11 ⇒ 〈x1,x1〉 | t12 ⇒ 〈x1,x2〉 | t13 ⇒ 〈x1,x3〉
  | t14 ⇒ 〈x1,x4〉 | t15 ⇒ 〈x1,x5〉 | t16 ⇒ 〈x1,x6〉 | t17 ⇒ 〈x1,x7〉
  | t18 ⇒ 〈x1,x8〉 | t19 ⇒ 〈x1,x9〉 | t1A ⇒ 〈x1,xA〉 | t1B ⇒ 〈x1,xB〉
  | t1C ⇒ 〈x1,xC〉 | t1D ⇒ 〈x1,xD〉 | t1E ⇒ 〈x1,xE〉 | t1F ⇒ 〈x1,xF〉 ].

coercion byte8_of_bitrigesim.

(* iteratore sui bitrigesimali *)
definition forall_bitrigesim ≝ λP.
 P t00 ⊗ P t01 ⊗ P t02 ⊗ P t03 ⊗ P t04 ⊗ P t05 ⊗ P t06 ⊗ P t07 ⊗
 P t08 ⊗ P t09 ⊗ P t0A ⊗ P t0B ⊗ P t0C ⊗ P t0D ⊗ P t0E ⊗ P t0F ⊗
 P t10 ⊗ P t11 ⊗ P t12 ⊗ P t13 ⊗ P t14 ⊗ P t15 ⊗ P t16 ⊗ P t17 ⊗
 P t18 ⊗ P t19 ⊗ P t1A ⊗ P t1B ⊗ P t1C ⊗ P t1D ⊗ P t1E ⊗ P t1F.
