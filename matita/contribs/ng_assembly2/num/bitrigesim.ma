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

include "common/comp.ma".
include "num/bool_lemmas.ma".

(* ************* *)
(* BITRIGESIMALI *)
(* ************* *)

ninductive bitrigesim : Type ≝
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

(* operatore = *)
ndefinition eq_bit ≝
λt1,t2:bitrigesim.
 match t1 with
  [ t00 ⇒ match t2 with [ t00 ⇒ true | _ ⇒ false ] | t01 ⇒ match t2 with [ t01 ⇒ true | _ ⇒ false ]
  | t02 ⇒ match t2 with [ t02 ⇒ true | _ ⇒ false ] | t03 ⇒ match t2 with [ t03 ⇒ true | _ ⇒ false ]
  | t04 ⇒ match t2 with [ t04 ⇒ true | _ ⇒ false ] | t05 ⇒ match t2 with [ t05 ⇒ true | _ ⇒ false ]
  | t06 ⇒ match t2 with [ t06 ⇒ true | _ ⇒ false ] | t07 ⇒ match t2 with [ t07 ⇒ true | _ ⇒ false ]
  | t08 ⇒ match t2 with [ t08 ⇒ true | _ ⇒ false ] | t09 ⇒ match t2 with [ t09 ⇒ true | _ ⇒ false ]
  | t0A ⇒ match t2 with [ t0A ⇒ true | _ ⇒ false ] | t0B ⇒ match t2 with [ t0B ⇒ true | _ ⇒ false ]
  | t0C ⇒ match t2 with [ t0C ⇒ true | _ ⇒ false ] | t0D ⇒ match t2 with [ t0D ⇒ true | _ ⇒ false ]
  | t0E ⇒ match t2 with [ t0E ⇒ true | _ ⇒ false ] | t0F ⇒ match t2 with [ t0F ⇒ true | _ ⇒ false ]
  | t10 ⇒ match t2 with [ t10 ⇒ true | _ ⇒ false ] | t11 ⇒ match t2 with [ t11 ⇒ true | _ ⇒ false ]
  | t12 ⇒ match t2 with [ t12 ⇒ true | _ ⇒ false ] | t13 ⇒ match t2 with [ t13 ⇒ true | _ ⇒ false ]
  | t14 ⇒ match t2 with [ t14 ⇒ true | _ ⇒ false ] | t15 ⇒ match t2 with [ t15 ⇒ true | _ ⇒ false ]
  | t16 ⇒ match t2 with [ t16 ⇒ true | _ ⇒ false ] | t17 ⇒ match t2 with [ t17 ⇒ true | _ ⇒ false ]
  | t18 ⇒ match t2 with [ t18 ⇒ true | _ ⇒ false ] | t19 ⇒ match t2 with [ t19 ⇒ true | _ ⇒ false ]
  | t1A ⇒ match t2 with [ t1A ⇒ true | _ ⇒ false ] | t1B ⇒ match t2 with [ t1B ⇒ true | _ ⇒ false ]
  | t1C ⇒ match t2 with [ t1C ⇒ true | _ ⇒ false ] | t1D ⇒ match t2 with [ t1D ⇒ true | _ ⇒ false ]
  | t1E ⇒ match t2 with [ t1E ⇒ true | _ ⇒ false ] | t1F ⇒ match t2 with [ t1F ⇒ true | _ ⇒ false ]
  ].

(* iteratore sui bitrigesimali *)
ndefinition forall_bit ≝ λP.
 P t00 ⊗ P t01 ⊗ P t02 ⊗ P t03 ⊗ P t04 ⊗ P t05 ⊗ P t06 ⊗ P t07 ⊗
 P t08 ⊗ P t09 ⊗ P t0A ⊗ P t0B ⊗ P t0C ⊗ P t0D ⊗ P t0E ⊗ P t0F ⊗
 P t10 ⊗ P t11 ⊗ P t12 ⊗ P t13 ⊗ P t14 ⊗ P t15 ⊗ P t16 ⊗ P t17 ⊗
 P t18 ⊗ P t19 ⊗ P t1A ⊗ P t1B ⊗ P t1C ⊗ P t1D ⊗ P t1E ⊗ P t1F.

(* operatore and *)
ndefinition and_bit ≝
λe1,e2.match e1 with
 [ t00 ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t00 | t02 ⇒ t00 | t03 ⇒ t00 | t04 ⇒ t00 | t05 ⇒ t00 | t06 ⇒ t00 | t07 ⇒ t00
  | t08 ⇒ t00 | t09 ⇒ t00 | t0A ⇒ t00 | t0B ⇒ t00 | t0C ⇒ t00 | t0D ⇒ t00 | t0E ⇒ t00 | t0F ⇒ t00
  | t10 ⇒ t00 | t11 ⇒ t00 | t12 ⇒ t00 | t13 ⇒ t00 | t14 ⇒ t00 | t15 ⇒ t00 | t16 ⇒ t00 | t17 ⇒ t00
  | t18 ⇒ t00 | t19 ⇒ t00 | t1A ⇒ t00 | t1B ⇒ t00 | t1C ⇒ t00 | t1D ⇒ t00 | t1E ⇒ t00 | t1F ⇒ t00 ]
 | t01 ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t01 | t02 ⇒ t00 | t03 ⇒ t01 | t04 ⇒ t00 | t05 ⇒ t01 | t06 ⇒ t00 | t07 ⇒ t01
  | t08 ⇒ t00 | t09 ⇒ t01 | t0A ⇒ t00 | t0B ⇒ t01 | t0C ⇒ t00 | t0D ⇒ t01 | t0E ⇒ t00 | t0F ⇒ t01
  | t10 ⇒ t00 | t11 ⇒ t01 | t12 ⇒ t00 | t13 ⇒ t01 | t14 ⇒ t00 | t15 ⇒ t01 | t16 ⇒ t00 | t17 ⇒ t01
  | t18 ⇒ t00 | t19 ⇒ t01 | t1A ⇒ t00 | t1B ⇒ t01 | t1C ⇒ t00 | t1D ⇒ t01 | t1E ⇒ t00 | t1F ⇒ t01 ]
 | t02 ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t00 | t02 ⇒ t02 | t03 ⇒ t02 | t04 ⇒ t00 | t05 ⇒ t00 | t06 ⇒ t02 | t07 ⇒ t02
  | t08 ⇒ t00 | t09 ⇒ t00 | t0A ⇒ t02 | t0B ⇒ t02 | t0C ⇒ t00 | t0D ⇒ t00 | t0E ⇒ t02 | t0F ⇒ t02
  | t10 ⇒ t00 | t11 ⇒ t00 | t12 ⇒ t02 | t13 ⇒ t02 | t14 ⇒ t00 | t15 ⇒ t00 | t16 ⇒ t02 | t17 ⇒ t02
  | t18 ⇒ t00 | t19 ⇒ t00 | t1A ⇒ t02 | t1B ⇒ t02 | t1C ⇒ t00 | t1D ⇒ t00 | t1E ⇒ t02 | t1F ⇒ t02 ]
 | t03 ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t01 | t02 ⇒ t02 | t03 ⇒ t03 | t04 ⇒ t00 | t05 ⇒ t01 | t06 ⇒ t02 | t07 ⇒ t03
  | t08 ⇒ t00 | t09 ⇒ t01 | t0A ⇒ t02 | t0B ⇒ t03 | t0C ⇒ t00 | t0D ⇒ t01 | t0E ⇒ t02 | t0F ⇒ t03
  | t10 ⇒ t00 | t11 ⇒ t01 | t12 ⇒ t02 | t13 ⇒ t03 | t14 ⇒ t00 | t15 ⇒ t01 | t16 ⇒ t02 | t17 ⇒ t03
  | t18 ⇒ t00 | t19 ⇒ t01 | t1A ⇒ t02 | t1B ⇒ t03 | t1C ⇒ t00 | t1D ⇒ t01 | t1E ⇒ t02 | t1F ⇒ t03 ]
 | t04 ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t00 | t02 ⇒ t00 | t03 ⇒ t00 | t04 ⇒ t04 | t05 ⇒ t04 | t06 ⇒ t04 | t07 ⇒ t04
  | t08 ⇒ t00 | t09 ⇒ t00 | t0A ⇒ t00 | t0B ⇒ t00 | t0C ⇒ t04 | t0D ⇒ t04 | t0E ⇒ t04 | t0F ⇒ t04
  | t10 ⇒ t00 | t11 ⇒ t00 | t12 ⇒ t00 | t13 ⇒ t00 | t14 ⇒ t04 | t15 ⇒ t04 | t16 ⇒ t04 | t17 ⇒ t04
  | t18 ⇒ t00 | t19 ⇒ t00 | t1A ⇒ t00 | t1B ⇒ t00 | t1C ⇒ t04 | t1D ⇒ t04 | t1E ⇒ t04 | t1F ⇒ t04 ]
 | t05 ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t01 | t02 ⇒ t00 | t03 ⇒ t01 | t04 ⇒ t04 | t05 ⇒ t05 | t06 ⇒ t04 | t07 ⇒ t05
  | t08 ⇒ t00 | t09 ⇒ t01 | t0A ⇒ t00 | t0B ⇒ t01 | t0C ⇒ t04 | t0D ⇒ t05 | t0E ⇒ t04 | t0F ⇒ t05
  | t10 ⇒ t00 | t11 ⇒ t01 | t12 ⇒ t00 | t13 ⇒ t01 | t14 ⇒ t04 | t15 ⇒ t05 | t16 ⇒ t04 | t17 ⇒ t05
  | t18 ⇒ t00 | t19 ⇒ t01 | t1A ⇒ t00 | t1B ⇒ t01 | t1C ⇒ t04 | t1D ⇒ t05 | t1E ⇒ t04 | t1F ⇒ t05 ]
 | t06 ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t00 | t02 ⇒ t02 | t03 ⇒ t02 | t04 ⇒ t04 | t05 ⇒ t04 | t06 ⇒ t06 | t07 ⇒ t06
  | t08 ⇒ t00 | t09 ⇒ t00 | t0A ⇒ t02 | t0B ⇒ t02 | t0C ⇒ t04 | t0D ⇒ t04 | t0E ⇒ t06 | t0F ⇒ t06
  | t10 ⇒ t00 | t11 ⇒ t00 | t12 ⇒ t02 | t13 ⇒ t02 | t14 ⇒ t04 | t15 ⇒ t04 | t16 ⇒ t06 | t17 ⇒ t06
  | t18 ⇒ t00 | t19 ⇒ t00 | t1A ⇒ t02 | t1B ⇒ t02 | t1C ⇒ t04 | t1D ⇒ t04 | t1E ⇒ t06 | t1F ⇒ t06 ]
 | t07 ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t01 | t02 ⇒ t02 | t03 ⇒ t03 | t04 ⇒ t04 | t05 ⇒ t05 | t06 ⇒ t06 | t07 ⇒ t07
  | t08 ⇒ t00 | t09 ⇒ t01 | t0A ⇒ t02 | t0B ⇒ t03 | t0C ⇒ t04 | t0D ⇒ t05 | t0E ⇒ t06 | t0F ⇒ t07
  | t10 ⇒ t00 | t11 ⇒ t01 | t12 ⇒ t02 | t13 ⇒ t03 | t14 ⇒ t04 | t15 ⇒ t05 | t16 ⇒ t06 | t17 ⇒ t07
  | t18 ⇒ t00 | t19 ⇒ t01 | t1A ⇒ t02 | t1B ⇒ t03 | t1C ⇒ t04 | t1D ⇒ t05 | t1E ⇒ t06 | t1F ⇒ t07 ]
 | t08 ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t00 | t02 ⇒ t00 | t03 ⇒ t00 | t04 ⇒ t00 | t05 ⇒ t00 | t06 ⇒ t00 | t07 ⇒ t00
  | t08 ⇒ t08 | t09 ⇒ t08 | t0A ⇒ t08 | t0B ⇒ t08 | t0C ⇒ t08 | t0D ⇒ t08 | t0E ⇒ t08 | t0F ⇒ t08
  | t10 ⇒ t00 | t11 ⇒ t00 | t12 ⇒ t00 | t13 ⇒ t00 | t14 ⇒ t00 | t15 ⇒ t00 | t16 ⇒ t00 | t17 ⇒ t00
  | t18 ⇒ t08 | t19 ⇒ t08 | t1A ⇒ t08 | t1B ⇒ t08 | t1C ⇒ t08 | t1D ⇒ t08 | t1E ⇒ t08 | t1F ⇒ t08 ]
 | t09 ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t01 | t02 ⇒ t00 | t03 ⇒ t01 | t04 ⇒ t00 | t05 ⇒ t01 | t06 ⇒ t00 | t07 ⇒ t01
  | t08 ⇒ t08 | t09 ⇒ t09 | t0A ⇒ t08 | t0B ⇒ t09 | t0C ⇒ t08 | t0D ⇒ t09 | t0E ⇒ t08 | t0F ⇒ t09
  | t10 ⇒ t00 | t11 ⇒ t01 | t12 ⇒ t00 | t13 ⇒ t01 | t14 ⇒ t00 | t15 ⇒ t01 | t16 ⇒ t00 | t17 ⇒ t01
  | t18 ⇒ t08 | t19 ⇒ t09 | t1A ⇒ t08 | t1B ⇒ t09 | t1C ⇒ t08 | t1D ⇒ t09 | t1E ⇒ t08 | t1F ⇒ t09 ]
 | t0A ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t00 | t02 ⇒ t02 | t03 ⇒ t02 | t04 ⇒ t00 | t05 ⇒ t00 | t06 ⇒ t02 | t07 ⇒ t02
  | t08 ⇒ t08 | t09 ⇒ t08 | t0A ⇒ t0A | t0B ⇒ t0A | t0C ⇒ t08 | t0D ⇒ t08 | t0E ⇒ t0A | t0F ⇒ t0A
  | t10 ⇒ t00 | t11 ⇒ t00 | t12 ⇒ t02 | t13 ⇒ t02 | t14 ⇒ t00 | t15 ⇒ t00 | t16 ⇒ t02 | t17 ⇒ t02
  | t18 ⇒ t08 | t19 ⇒ t08 | t1A ⇒ t0A | t1B ⇒ t0A | t1C ⇒ t08 | t1D ⇒ t08 | t1E ⇒ t0A | t1F ⇒ t0A ]
 | t0B ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t01 | t02 ⇒ t02 | t03 ⇒ t03 | t04 ⇒ t00 | t05 ⇒ t01 | t06 ⇒ t02 | t07 ⇒ t03
  | t08 ⇒ t08 | t09 ⇒ t09 | t0A ⇒ t0A | t0B ⇒ t0B | t0C ⇒ t08 | t0D ⇒ t09 | t0E ⇒ t0A | t0F ⇒ t0B
  | t10 ⇒ t00 | t11 ⇒ t01 | t12 ⇒ t02 | t13 ⇒ t03 | t14 ⇒ t00 | t15 ⇒ t01 | t16 ⇒ t02 | t17 ⇒ t03
  | t18 ⇒ t08 | t19 ⇒ t09 | t1A ⇒ t0A | t1B ⇒ t0B | t1C ⇒ t08 | t1D ⇒ t09 | t1E ⇒ t0A | t1F ⇒ t0B ]
 | t0C ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t00 | t02 ⇒ t00 | t03 ⇒ t00 | t04 ⇒ t04 | t05 ⇒ t04 | t06 ⇒ t04 | t07 ⇒ t04
  | t08 ⇒ t08 | t09 ⇒ t08 | t0A ⇒ t08 | t0B ⇒ t08 | t0C ⇒ t0C | t0D ⇒ t0C | t0E ⇒ t0C | t0F ⇒ t0C
  | t10 ⇒ t00 | t11 ⇒ t00 | t12 ⇒ t00 | t13 ⇒ t00 | t14 ⇒ t04 | t15 ⇒ t04 | t16 ⇒ t04 | t17 ⇒ t04
  | t18 ⇒ t08 | t19 ⇒ t08 | t1A ⇒ t08 | t1B ⇒ t08 | t1C ⇒ t0C | t1D ⇒ t0C | t1E ⇒ t0C | t1F ⇒ t0C ]
 | t0D ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t01 | t02 ⇒ t00 | t03 ⇒ t01 | t04 ⇒ t04 | t05 ⇒ t05 | t06 ⇒ t04 | t07 ⇒ t05
  | t08 ⇒ t08 | t09 ⇒ t09 | t0A ⇒ t08 | t0B ⇒ t09 | t0C ⇒ t0C | t0D ⇒ t0D | t0E ⇒ t0C | t0F ⇒ t0D
  | t10 ⇒ t00 | t11 ⇒ t01 | t12 ⇒ t00 | t13 ⇒ t01 | t14 ⇒ t04 | t15 ⇒ t05 | t16 ⇒ t04 | t17 ⇒ t05
  | t18 ⇒ t08 | t19 ⇒ t09 | t1A ⇒ t08 | t1B ⇒ t09 | t1C ⇒ t0C | t1D ⇒ t0D | t1E ⇒ t0C | t1F ⇒ t0D ]
 | t0E ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t00 | t02 ⇒ t02 | t03 ⇒ t02 | t04 ⇒ t04 | t05 ⇒ t04 | t06 ⇒ t06 | t07 ⇒ t06
  | t08 ⇒ t08 | t09 ⇒ t08 | t0A ⇒ t0A | t0B ⇒ t0A | t0C ⇒ t0C | t0D ⇒ t0C | t0E ⇒ t0E | t0F ⇒ t0E
  | t10 ⇒ t00 | t11 ⇒ t00 | t12 ⇒ t02 | t13 ⇒ t02 | t14 ⇒ t04 | t15 ⇒ t04 | t16 ⇒ t06 | t17 ⇒ t06
  | t18 ⇒ t08 | t19 ⇒ t08 | t1A ⇒ t0A | t1B ⇒ t0A | t1C ⇒ t0C | t1D ⇒ t0C | t1E ⇒ t0E | t1F ⇒ t0E ]
 | t0F ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t01 | t02 ⇒ t02 | t03 ⇒ t03 | t04 ⇒ t04 | t05 ⇒ t05 | t06 ⇒ t06 | t07 ⇒ t07
  | t08 ⇒ t08 | t09 ⇒ t09 | t0A ⇒ t0A | t0B ⇒ t0B | t0C ⇒ t0C | t0D ⇒ t0D | t0E ⇒ t0E | t0F ⇒ t0F
  | t10 ⇒ t00 | t11 ⇒ t01 | t12 ⇒ t02 | t13 ⇒ t03 | t14 ⇒ t04 | t15 ⇒ t05 | t16 ⇒ t06 | t17 ⇒ t07
  | t18 ⇒ t08 | t19 ⇒ t09 | t1A ⇒ t0A | t1B ⇒ t0B | t1C ⇒ t0C | t1D ⇒ t0D | t1E ⇒ t0E | t1F ⇒ t0F ]
 | t10 ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t00 | t02 ⇒ t00 | t03 ⇒ t00 | t04 ⇒ t00 | t05 ⇒ t00 | t06 ⇒ t00 | t07 ⇒ t00
  | t08 ⇒ t00 | t09 ⇒ t00 | t0A ⇒ t00 | t0B ⇒ t00 | t0C ⇒ t00 | t0D ⇒ t00 | t0E ⇒ t00 | t0F ⇒ t00
  | t10 ⇒ t10 | t11 ⇒ t10 | t12 ⇒ t10 | t13 ⇒ t10 | t14 ⇒ t10 | t15 ⇒ t10 | t16 ⇒ t10 | t17 ⇒ t10
  | t18 ⇒ t10 | t19 ⇒ t10 | t1A ⇒ t10 | t1B ⇒ t10 | t1C ⇒ t10 | t1D ⇒ t10 | t1E ⇒ t10 | t1F ⇒ t10 ]
 | t11 ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t01 | t02 ⇒ t00 | t03 ⇒ t01 | t04 ⇒ t00 | t05 ⇒ t01 | t06 ⇒ t00 | t07 ⇒ t01
  | t08 ⇒ t00 | t09 ⇒ t01 | t0A ⇒ t00 | t0B ⇒ t01 | t0C ⇒ t00 | t0D ⇒ t01 | t0E ⇒ t00 | t0F ⇒ t01
  | t10 ⇒ t10 | t11 ⇒ t11 | t12 ⇒ t10 | t13 ⇒ t11 | t14 ⇒ t10 | t15 ⇒ t11 | t16 ⇒ t10 | t17 ⇒ t11
  | t18 ⇒ t10 | t19 ⇒ t11 | t1A ⇒ t10 | t1B ⇒ t11 | t1C ⇒ t10 | t1D ⇒ t11 | t1E ⇒ t10 | t1F ⇒ t11 ]
 | t12 ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t00 | t02 ⇒ t02 | t03 ⇒ t02 | t04 ⇒ t00 | t05 ⇒ t00 | t06 ⇒ t02 | t07 ⇒ t02
  | t08 ⇒ t00 | t09 ⇒ t00 | t0A ⇒ t02 | t0B ⇒ t02 | t0C ⇒ t00 | t0D ⇒ t00 | t0E ⇒ t02 | t0F ⇒ t02
  | t10 ⇒ t10 | t11 ⇒ t10 | t12 ⇒ t12 | t13 ⇒ t12 | t14 ⇒ t10 | t15 ⇒ t10 | t16 ⇒ t12 | t17 ⇒ t12
  | t18 ⇒ t10 | t19 ⇒ t10 | t1A ⇒ t12 | t1B ⇒ t12 | t1C ⇒ t10 | t1D ⇒ t10 | t1E ⇒ t12 | t1F ⇒ t12 ]
 | t13 ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t01 | t02 ⇒ t02 | t03 ⇒ t03 | t04 ⇒ t00 | t05 ⇒ t01 | t06 ⇒ t02 | t07 ⇒ t03
  | t08 ⇒ t00 | t09 ⇒ t01 | t0A ⇒ t02 | t0B ⇒ t03 | t0C ⇒ t00 | t0D ⇒ t01 | t0E ⇒ t02 | t0F ⇒ t03
  | t10 ⇒ t10 | t11 ⇒ t11 | t12 ⇒ t12 | t13 ⇒ t13 | t14 ⇒ t10 | t15 ⇒ t11 | t16 ⇒ t12 | t17 ⇒ t13
  | t18 ⇒ t10 | t19 ⇒ t11 | t1A ⇒ t12 | t1B ⇒ t13 | t1C ⇒ t10 | t1D ⇒ t11 | t1E ⇒ t12 | t1F ⇒ t13 ]
 | t14 ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t00 | t02 ⇒ t00 | t03 ⇒ t00 | t04 ⇒ t04 | t05 ⇒ t04 | t06 ⇒ t04 | t07 ⇒ t04
  | t08 ⇒ t00 | t09 ⇒ t00 | t0A ⇒ t00 | t0B ⇒ t00 | t0C ⇒ t04 | t0D ⇒ t04 | t0E ⇒ t04 | t0F ⇒ t04
  | t10 ⇒ t10 | t11 ⇒ t10 | t12 ⇒ t10 | t13 ⇒ t10 | t14 ⇒ t14 | t15 ⇒ t14 | t16 ⇒ t14 | t17 ⇒ t14
  | t18 ⇒ t10 | t19 ⇒ t10 | t1A ⇒ t10 | t1B ⇒ t10 | t1C ⇒ t14 | t1D ⇒ t14 | t1E ⇒ t14 | t1F ⇒ t14 ]
 | t15 ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t01 | t02 ⇒ t00 | t03 ⇒ t01 | t04 ⇒ t04 | t05 ⇒ t05 | t06 ⇒ t04 | t07 ⇒ t05
  | t08 ⇒ t00 | t09 ⇒ t01 | t0A ⇒ t00 | t0B ⇒ t01 | t0C ⇒ t04 | t0D ⇒ t05 | t0E ⇒ t04 | t0F ⇒ t05
  | t10 ⇒ t10 | t11 ⇒ t11 | t12 ⇒ t10 | t13 ⇒ t11 | t14 ⇒ t14 | t15 ⇒ t15 | t16 ⇒ t14 | t17 ⇒ t15
  | t18 ⇒ t10 | t19 ⇒ t11 | t1A ⇒ t10 | t1B ⇒ t11 | t1C ⇒ t14 | t1D ⇒ t15 | t1E ⇒ t14 | t1F ⇒ t15 ]
 | t16 ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t00 | t02 ⇒ t02 | t03 ⇒ t02 | t04 ⇒ t04 | t05 ⇒ t04 | t06 ⇒ t06 | t07 ⇒ t06
  | t08 ⇒ t00 | t09 ⇒ t00 | t0A ⇒ t02 | t0B ⇒ t02 | t0C ⇒ t04 | t0D ⇒ t04 | t0E ⇒ t06 | t0F ⇒ t06
  | t10 ⇒ t10 | t11 ⇒ t10 | t12 ⇒ t12 | t13 ⇒ t12 | t14 ⇒ t14 | t15 ⇒ t14 | t16 ⇒ t16 | t17 ⇒ t16
  | t18 ⇒ t10 | t19 ⇒ t10 | t1A ⇒ t12 | t1B ⇒ t12 | t1C ⇒ t14 | t1D ⇒ t14 | t1E ⇒ t16 | t1F ⇒ t16 ]
 | t17 ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t01 | t02 ⇒ t02 | t03 ⇒ t03 | t04 ⇒ t04 | t05 ⇒ t05 | t06 ⇒ t06 | t07 ⇒ t07
  | t08 ⇒ t00 | t09 ⇒ t01 | t0A ⇒ t02 | t0B ⇒ t03 | t0C ⇒ t04 | t0D ⇒ t05 | t0E ⇒ t06 | t0F ⇒ t07
  | t10 ⇒ t10 | t11 ⇒ t11 | t12 ⇒ t12 | t13 ⇒ t13 | t14 ⇒ t14 | t15 ⇒ t15 | t16 ⇒ t16 | t17 ⇒ t17
  | t18 ⇒ t10 | t19 ⇒ t11 | t1A ⇒ t12 | t1B ⇒ t13 | t1C ⇒ t14 | t1D ⇒ t15 | t1E ⇒ t16 | t1F ⇒ t17 ]
 | t18 ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t00 | t02 ⇒ t00 | t03 ⇒ t00 | t04 ⇒ t00 | t05 ⇒ t00 | t06 ⇒ t00 | t07 ⇒ t00
  | t08 ⇒ t08 | t09 ⇒ t08 | t0A ⇒ t08 | t0B ⇒ t08 | t0C ⇒ t08 | t0D ⇒ t08 | t0E ⇒ t08 | t0F ⇒ t08
  | t10 ⇒ t10 | t11 ⇒ t10 | t12 ⇒ t10 | t13 ⇒ t10 | t14 ⇒ t10 | t15 ⇒ t10 | t16 ⇒ t10 | t17 ⇒ t10
  | t18 ⇒ t18 | t19 ⇒ t18 | t1A ⇒ t18 | t1B ⇒ t18 | t1C ⇒ t18 | t1D ⇒ t18 | t1E ⇒ t18 | t1F ⇒ t18 ]
 | t19 ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t01 | t02 ⇒ t00 | t03 ⇒ t01 | t04 ⇒ t00 | t05 ⇒ t01 | t06 ⇒ t00 | t07 ⇒ t01
  | t08 ⇒ t08 | t09 ⇒ t09 | t0A ⇒ t08 | t0B ⇒ t09 | t0C ⇒ t08 | t0D ⇒ t09 | t0E ⇒ t08 | t0F ⇒ t09
  | t10 ⇒ t10 | t11 ⇒ t11 | t12 ⇒ t10 | t13 ⇒ t11 | t14 ⇒ t10 | t15 ⇒ t11 | t16 ⇒ t10 | t17 ⇒ t11
  | t18 ⇒ t18 | t19 ⇒ t19 | t1A ⇒ t18 | t1B ⇒ t19 | t1C ⇒ t18 | t1D ⇒ t19 | t1E ⇒ t18 | t1F ⇒ t19 ]
 | t1A ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t00 | t02 ⇒ t02 | t03 ⇒ t02 | t04 ⇒ t00 | t05 ⇒ t00 | t06 ⇒ t02 | t07 ⇒ t02
  | t08 ⇒ t08 | t09 ⇒ t08 | t0A ⇒ t0A | t0B ⇒ t0A | t0C ⇒ t08 | t0D ⇒ t08 | t0E ⇒ t0A | t0F ⇒ t0A
  | t10 ⇒ t10 | t11 ⇒ t10 | t12 ⇒ t12 | t13 ⇒ t12 | t14 ⇒ t10 | t15 ⇒ t10 | t16 ⇒ t12 | t17 ⇒ t12
  | t18 ⇒ t18 | t19 ⇒ t18 | t1A ⇒ t1A | t1B ⇒ t1A | t1C ⇒ t18 | t1D ⇒ t18 | t1E ⇒ t1A | t1F ⇒ t1A ]
 | t1B ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t01 | t02 ⇒ t02 | t03 ⇒ t03 | t04 ⇒ t00 | t05 ⇒ t01 | t06 ⇒ t02 | t07 ⇒ t03
  | t08 ⇒ t08 | t09 ⇒ t09 | t0A ⇒ t0A | t0B ⇒ t0B | t0C ⇒ t08 | t0D ⇒ t09 | t0E ⇒ t0A | t0F ⇒ t0B
  | t10 ⇒ t10 | t11 ⇒ t11 | t12 ⇒ t12 | t13 ⇒ t13 | t14 ⇒ t10 | t15 ⇒ t11 | t16 ⇒ t12 | t17 ⇒ t13
  | t18 ⇒ t18 | t19 ⇒ t19 | t1A ⇒ t1A | t1B ⇒ t1B | t1C ⇒ t18 | t1D ⇒ t19 | t1E ⇒ t1A | t1F ⇒ t1B ]
 | t1C ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t00 | t02 ⇒ t00 | t03 ⇒ t00 | t04 ⇒ t04 | t05 ⇒ t04 | t06 ⇒ t04 | t07 ⇒ t04
  | t08 ⇒ t08 | t09 ⇒ t08 | t0A ⇒ t08 | t0B ⇒ t08 | t0C ⇒ t0C | t0D ⇒ t0C | t0E ⇒ t0C | t0F ⇒ t0C
  | t10 ⇒ t10 | t11 ⇒ t10 | t12 ⇒ t10 | t13 ⇒ t10 | t14 ⇒ t14 | t15 ⇒ t14 | t16 ⇒ t14 | t17 ⇒ t14
  | t18 ⇒ t18 | t19 ⇒ t18 | t1A ⇒ t18 | t1B ⇒ t18 | t1C ⇒ t1C | t1D ⇒ t1C | t1E ⇒ t1C | t1F ⇒ t1C ]
 | t1D ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t01 | t02 ⇒ t00 | t03 ⇒ t01 | t04 ⇒ t04 | t05 ⇒ t05 | t06 ⇒ t04 | t07 ⇒ t05
  | t08 ⇒ t08 | t09 ⇒ t09 | t0A ⇒ t08 | t0B ⇒ t09 | t0C ⇒ t0C | t0D ⇒ t0D | t0E ⇒ t0C | t0F ⇒ t0D
  | t10 ⇒ t10 | t11 ⇒ t11 | t12 ⇒ t10 | t13 ⇒ t11 | t14 ⇒ t14 | t15 ⇒ t15 | t16 ⇒ t14 | t17 ⇒ t15
  | t18 ⇒ t18 | t19 ⇒ t19 | t1A ⇒ t18 | t1B ⇒ t19 | t1C ⇒ t1C | t1D ⇒ t1D | t1E ⇒ t1C | t1F ⇒ t1D ]
 | t1E ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t00 | t02 ⇒ t02 | t03 ⇒ t02 | t04 ⇒ t04 | t05 ⇒ t04 | t06 ⇒ t06 | t07 ⇒ t06
  | t08 ⇒ t08 | t09 ⇒ t08 | t0A ⇒ t0A | t0B ⇒ t0A | t0C ⇒ t0C | t0D ⇒ t0C | t0E ⇒ t0E | t0F ⇒ t0E
  | t10 ⇒ t10 | t11 ⇒ t10 | t12 ⇒ t12 | t13 ⇒ t12 | t14 ⇒ t14 | t15 ⇒ t14 | t16 ⇒ t16 | t17 ⇒ t16
  | t18 ⇒ t18 | t19 ⇒ t18 | t1A ⇒ t1A | t1B ⇒ t1A | t1C ⇒ t1C | t1D ⇒ t1C | t1E ⇒ t1E | t1F ⇒ t1E ]
 | t1F ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t01 | t02 ⇒ t02 | t03 ⇒ t03 | t04 ⇒ t04 | t05 ⇒ t05 | t06 ⇒ t06 | t07 ⇒ t07
  | t08 ⇒ t08 | t09 ⇒ t09 | t0A ⇒ t0A | t0B ⇒ t0B | t0C ⇒ t0C | t0D ⇒ t0D | t0E ⇒ t0E | t0F ⇒ t0F
  | t10 ⇒ t10 | t11 ⇒ t11 | t12 ⇒ t12 | t13 ⇒ t13 | t14 ⇒ t14 | t15 ⇒ t15 | t16 ⇒ t16 | t17 ⇒ t17
  | t18 ⇒ t18 | t19 ⇒ t19 | t1A ⇒ t1A | t1B ⇒ t1B | t1C ⇒ t1C | t1D ⇒ t1D | t1E ⇒ t1E | t1F ⇒ t1F ]
 ]. 

(* operatore or *)
ndefinition or_bit ≝
λe1,e2.match e1 with
 [ t00 ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t01 | t02 ⇒ t02 | t03 ⇒ t03 | t04 ⇒ t04 | t05 ⇒ t05 | t06 ⇒ t06 | t07 ⇒ t07
  | t08 ⇒ t08 | t09 ⇒ t09 | t0A ⇒ t0A | t0B ⇒ t0B | t0C ⇒ t0C | t0D ⇒ t0D | t0E ⇒ t0E | t0F ⇒ t0F
  | t10 ⇒ t10 | t11 ⇒ t11 | t12 ⇒ t12 | t13 ⇒ t13 | t14 ⇒ t14 | t15 ⇒ t15 | t16 ⇒ t16 | t17 ⇒ t17
  | t18 ⇒ t18 | t19 ⇒ t19 | t1A ⇒ t1A | t1B ⇒ t1B | t1C ⇒ t1C | t1D ⇒ t1D | t1E ⇒ t1E | t1F ⇒ t1F ]
 | t01 ⇒ match e2 with
  [ t00 ⇒ t01 | t01 ⇒ t01 | t02 ⇒ t03 | t03 ⇒ t03 | t04 ⇒ t05 | t05 ⇒ t05 | t06 ⇒ t07 | t07 ⇒ t07
  | t08 ⇒ t09 | t09 ⇒ t09 | t0A ⇒ t0B | t0B ⇒ t0B | t0C ⇒ t0D | t0D ⇒ t0D | t0E ⇒ t0F | t0F ⇒ t0F
  | t10 ⇒ t11 | t11 ⇒ t11 | t12 ⇒ t13 | t13 ⇒ t13 | t14 ⇒ t15 | t15 ⇒ t15 | t16 ⇒ t17 | t17 ⇒ t17
  | t18 ⇒ t19 | t19 ⇒ t19 | t1A ⇒ t1B | t1B ⇒ t1B | t1C ⇒ t1D | t1D ⇒ t1D | t1E ⇒ t1F | t1F ⇒ t1F ]
 | t02 ⇒ match e2 with
  [ t00 ⇒ t02 | t01 ⇒ t03 | t02 ⇒ t02 | t03 ⇒ t03 | t04 ⇒ t06 | t05 ⇒ t07 | t06 ⇒ t06 | t07 ⇒ t07
  | t08 ⇒ t0A | t09 ⇒ t0B | t0A ⇒ t0A | t0B ⇒ t0B | t0C ⇒ t0E | t0D ⇒ t0F | t0E ⇒ t0E | t0F ⇒ t0F
  | t10 ⇒ t12 | t11 ⇒ t13 | t12 ⇒ t12 | t13 ⇒ t13 | t14 ⇒ t16 | t15 ⇒ t17 | t16 ⇒ t16 | t17 ⇒ t17
  | t18 ⇒ t1A | t19 ⇒ t1B | t1A ⇒ t1A | t1B ⇒ t1B | t1C ⇒ t1E | t1D ⇒ t1F | t1E ⇒ t1E | t1F ⇒ t1F ]
 | t03 ⇒ match e2 with
  [ t00 ⇒ t03 | t01 ⇒ t03 | t02 ⇒ t03 | t03 ⇒ t03 | t04 ⇒ t07 | t05 ⇒ t07 | t06 ⇒ t07 | t07 ⇒ t07
  | t08 ⇒ t0B | t09 ⇒ t0B | t0A ⇒ t0B | t0B ⇒ t0B | t0C ⇒ t0F | t0D ⇒ t0F | t0E ⇒ t0F | t0F ⇒ t0F
  | t10 ⇒ t13 | t11 ⇒ t13 | t12 ⇒ t13 | t13 ⇒ t13 | t14 ⇒ t17 | t15 ⇒ t17 | t16 ⇒ t17 | t17 ⇒ t17
  | t18 ⇒ t1B | t19 ⇒ t1B | t1A ⇒ t1B | t1B ⇒ t1B | t1C ⇒ t1F | t1D ⇒ t1F | t1E ⇒ t1F | t1F ⇒ t1F ]
 | t04 ⇒ match e2 with
  [ t00 ⇒ t04 | t01 ⇒ t05 | t02 ⇒ t06 | t03 ⇒ t07 | t04 ⇒ t04 | t05 ⇒ t05 | t06 ⇒ t06 | t07 ⇒ t07
  | t08 ⇒ t0C | t09 ⇒ t0D | t0A ⇒ t0E | t0B ⇒ t0F | t0C ⇒ t0C | t0D ⇒ t0D | t0E ⇒ t0E | t0F ⇒ t0F
  | t10 ⇒ t14 | t11 ⇒ t15 | t12 ⇒ t16 | t13 ⇒ t17 | t14 ⇒ t14 | t15 ⇒ t15 | t16 ⇒ t16 | t17 ⇒ t17
  | t18 ⇒ t1C | t19 ⇒ t1D | t1A ⇒ t1E | t1B ⇒ t1F | t1C ⇒ t1C | t1D ⇒ t1D | t1E ⇒ t1E | t1F ⇒ t1F ]
 | t05 ⇒ match e2 with
  [ t00 ⇒ t05 | t01 ⇒ t05 | t02 ⇒ t07 | t03 ⇒ t07 | t04 ⇒ t05 | t05 ⇒ t05 | t06 ⇒ t07 | t07 ⇒ t07
  | t08 ⇒ t0D | t09 ⇒ t0D | t0A ⇒ t0F | t0B ⇒ t0F | t0C ⇒ t0D | t0D ⇒ t0D | t0E ⇒ t0F | t0F ⇒ t0F
  | t10 ⇒ t15 | t11 ⇒ t15 | t12 ⇒ t17 | t13 ⇒ t17 | t14 ⇒ t15 | t15 ⇒ t15 | t16 ⇒ t17 | t17 ⇒ t17
  | t18 ⇒ t1D | t19 ⇒ t1D | t1A ⇒ t1F | t1B ⇒ t1F | t1C ⇒ t1D | t1D ⇒ t1D | t1E ⇒ t1F | t1F ⇒ t1F ]
 | t06 ⇒ match e2 with
  [ t00 ⇒ t06 | t01 ⇒ t07 | t02 ⇒ t06 | t03 ⇒ t07 | t04 ⇒ t06 | t05 ⇒ t07 | t06 ⇒ t06 | t07 ⇒ t07
  | t08 ⇒ t0E | t09 ⇒ t0F | t0A ⇒ t0E | t0B ⇒ t0F | t0C ⇒ t0E | t0D ⇒ t0F | t0E ⇒ t0E | t0F ⇒ t0F
  | t10 ⇒ t16 | t11 ⇒ t17 | t12 ⇒ t16 | t13 ⇒ t17 | t14 ⇒ t16 | t15 ⇒ t17 | t16 ⇒ t16 | t17 ⇒ t17
  | t18 ⇒ t1E | t19 ⇒ t1F | t1A ⇒ t1E | t1B ⇒ t1F | t1C ⇒ t1E | t1D ⇒ t1F | t1E ⇒ t1E | t1F ⇒ t1F ]
 | t07 ⇒ match e2 with
  [ t00 ⇒ t07 | t01 ⇒ t07 | t02 ⇒ t07 | t03 ⇒ t07 | t04 ⇒ t07 | t05 ⇒ t07 | t06 ⇒ t07 | t07 ⇒ t07
  | t08 ⇒ t0F | t09 ⇒ t0F | t0A ⇒ t0F | t0B ⇒ t0F | t0C ⇒ t0F | t0D ⇒ t0F | t0E ⇒ t0F | t0F ⇒ t0F
  | t10 ⇒ t17 | t11 ⇒ t17 | t12 ⇒ t17 | t13 ⇒ t17 | t14 ⇒ t17 | t15 ⇒ t17 | t16 ⇒ t17 | t17 ⇒ t17
  | t18 ⇒ t1F | t19 ⇒ t1F | t1A ⇒ t1F | t1B ⇒ t1F | t1C ⇒ t1F | t1D ⇒ t1F | t1E ⇒ t1F | t1F ⇒ t1F ]
 | t08 ⇒ match e2 with
  [ t00 ⇒ t08 | t01 ⇒ t09 | t02 ⇒ t0A | t03 ⇒ t0B | t04 ⇒ t0C | t05 ⇒ t0D | t06 ⇒ t0E | t07 ⇒ t0F
  | t08 ⇒ t08 | t09 ⇒ t09 | t0A ⇒ t0A | t0B ⇒ t0B | t0C ⇒ t0C | t0D ⇒ t0D | t0E ⇒ t0E | t0F ⇒ t0F
  | t10 ⇒ t18 | t11 ⇒ t19 | t12 ⇒ t1A | t13 ⇒ t1B | t14 ⇒ t1C | t15 ⇒ t1D | t16 ⇒ t1E | t17 ⇒ t1F
  | t18 ⇒ t18 | t19 ⇒ t19 | t1A ⇒ t1A | t1B ⇒ t1B | t1C ⇒ t1C | t1D ⇒ t1D | t1E ⇒ t1E | t1F ⇒ t1F ]
 | t09 ⇒ match e2 with
  [ t00 ⇒ t09 | t01 ⇒ t09 | t02 ⇒ t0B | t03 ⇒ t0B | t04 ⇒ t0D | t05 ⇒ t0D | t06 ⇒ t0F | t07 ⇒ t0F
  | t08 ⇒ t09 | t09 ⇒ t09 | t0A ⇒ t0B | t0B ⇒ t0B | t0C ⇒ t0D | t0D ⇒ t0D | t0E ⇒ t0F | t0F ⇒ t0F
  | t10 ⇒ t19 | t11 ⇒ t19 | t12 ⇒ t1B | t13 ⇒ t1B | t14 ⇒ t1D | t15 ⇒ t1D | t16 ⇒ t1F | t17 ⇒ t1F
  | t18 ⇒ t19 | t19 ⇒ t19 | t1A ⇒ t1B | t1B ⇒ t1B | t1C ⇒ t1D | t1D ⇒ t1D | t1E ⇒ t1F | t1F ⇒ t1F ]
 | t0A ⇒ match e2 with
  [ t00 ⇒ t0A | t01 ⇒ t0B | t02 ⇒ t0A | t03 ⇒ t0B | t04 ⇒ t0E | t05 ⇒ t0F | t06 ⇒ t0E | t07 ⇒ t0F
  | t08 ⇒ t0A | t09 ⇒ t0B | t0A ⇒ t0A | t0B ⇒ t0B | t0C ⇒ t0E | t0D ⇒ t0F | t0E ⇒ t0E | t0F ⇒ t0F
  | t10 ⇒ t1A | t11 ⇒ t1B | t12 ⇒ t1A | t13 ⇒ t1B | t14 ⇒ t1E | t15 ⇒ t1F | t16 ⇒ t1E | t17 ⇒ t1F
  | t18 ⇒ t1A | t19 ⇒ t1B | t1A ⇒ t1A | t1B ⇒ t1B | t1C ⇒ t1E | t1D ⇒ t1F | t1E ⇒ t1E | t1F ⇒ t1F ]
 | t0B ⇒ match e2 with
  [ t00 ⇒ t0B | t01 ⇒ t0B | t02 ⇒ t0B | t03 ⇒ t0B | t04 ⇒ t0F | t05 ⇒ t0F | t06 ⇒ t0F | t07 ⇒ t0F
  | t08 ⇒ t0B | t09 ⇒ t0B | t0A ⇒ t0B | t0B ⇒ t0B | t0C ⇒ t0F | t0D ⇒ t0F | t0E ⇒ t0F | t0F ⇒ t0F
  | t10 ⇒ t1B | t11 ⇒ t1B | t12 ⇒ t1B | t13 ⇒ t1B | t14 ⇒ t1F | t15 ⇒ t1F | t16 ⇒ t1F | t17 ⇒ t1F
  | t18 ⇒ t1B | t19 ⇒ t1B | t1A ⇒ t1B | t1B ⇒ t1B | t1C ⇒ t1F | t1D ⇒ t1F | t1E ⇒ t1F | t1F ⇒ t1F ]
 | t0C ⇒ match e2 with
  [ t00 ⇒ t0C | t01 ⇒ t0D | t02 ⇒ t0E | t03 ⇒ t0F | t04 ⇒ t0C | t05 ⇒ t0D | t06 ⇒ t0E | t07 ⇒ t0F
  | t08 ⇒ t0C | t09 ⇒ t0D | t0A ⇒ t0E | t0B ⇒ t0F | t0C ⇒ t0C | t0D ⇒ t0D | t0E ⇒ t0E | t0F ⇒ t0F
  | t10 ⇒ t1C | t11 ⇒ t1D | t12 ⇒ t1E | t13 ⇒ t1F | t14 ⇒ t1C | t15 ⇒ t1D | t16 ⇒ t1E | t17 ⇒ t1F
  | t18 ⇒ t1C | t19 ⇒ t1D | t1A ⇒ t1E | t1B ⇒ t1F | t1C ⇒ t1C | t1D ⇒ t1D | t1E ⇒ t1E | t1F ⇒ t1F ]
 | t0D ⇒ match e2 with
  [ t00 ⇒ t0D | t01 ⇒ t0D | t02 ⇒ t0F | t03 ⇒ t0F | t04 ⇒ t0D | t05 ⇒ t0D | t06 ⇒ t0F | t07 ⇒ t0F
  | t08 ⇒ t0D | t09 ⇒ t0D | t0A ⇒ t0F | t0B ⇒ t0F | t0C ⇒ t0D | t0D ⇒ t0D | t0E ⇒ t0F | t0F ⇒ t0F
  | t10 ⇒ t1D | t11 ⇒ t1D | t12 ⇒ t1F | t13 ⇒ t1F | t14 ⇒ t1D | t15 ⇒ t1D | t16 ⇒ t1F | t17 ⇒ t1F
  | t18 ⇒ t1D | t19 ⇒ t1D | t1A ⇒ t1F | t1B ⇒ t1F | t1C ⇒ t1D | t1D ⇒ t1D | t1E ⇒ t1F | t1F ⇒ t1F ]
 | t0E ⇒ match e2 with
  [ t00 ⇒ t0E | t01 ⇒ t0F | t02 ⇒ t0E | t03 ⇒ t0F | t04 ⇒ t0E | t05 ⇒ t0F | t06 ⇒ t0E | t07 ⇒ t0F
  | t08 ⇒ t0E | t09 ⇒ t0F | t0A ⇒ t0E | t0B ⇒ t0F | t0C ⇒ t0E | t0D ⇒ t0F | t0E ⇒ t0E | t0F ⇒ t0F
  | t10 ⇒ t1E | t11 ⇒ t1F | t12 ⇒ t1E | t13 ⇒ t1F | t14 ⇒ t1E | t15 ⇒ t1F | t16 ⇒ t1E | t17 ⇒ t1F
  | t18 ⇒ t1E | t19 ⇒ t1F | t1A ⇒ t1E | t1B ⇒ t1F | t1C ⇒ t1E | t1D ⇒ t1F | t1E ⇒ t1E | t1F ⇒ t1F ]
 | t0F ⇒ match e2 with
  [ t00 ⇒ t0F | t01 ⇒ t0F | t02 ⇒ t0F | t03 ⇒ t0F | t04 ⇒ t0F | t05 ⇒ t0F | t06 ⇒ t0F | t07 ⇒ t0F
  | t08 ⇒ t0F | t09 ⇒ t0F | t0A ⇒ t0F | t0B ⇒ t0F | t0C ⇒ t0F | t0D ⇒ t0F | t0E ⇒ t0F | t0F ⇒ t0F
  | t10 ⇒ t1F | t11 ⇒ t1F | t12 ⇒ t1F | t13 ⇒ t1F | t14 ⇒ t1F | t15 ⇒ t1F | t16 ⇒ t1F | t17 ⇒ t1F
  | t18 ⇒ t1F | t19 ⇒ t1F | t1A ⇒ t1F | t1B ⇒ t1F | t1C ⇒ t1F | t1D ⇒ t1F | t1E ⇒ t1F | t1F ⇒ t1F ]
 | t10 ⇒ match e2 with
  [ t00 ⇒ t10 | t01 ⇒ t11 | t02 ⇒ t12 | t03 ⇒ t13 | t04 ⇒ t14 | t05 ⇒ t15 | t06 ⇒ t16 | t07 ⇒ t17
  | t08 ⇒ t18 | t09 ⇒ t19 | t0A ⇒ t1A | t0B ⇒ t1B | t0C ⇒ t1C | t0D ⇒ t1D | t0E ⇒ t1E | t0F ⇒ t1F
  | t10 ⇒ t10 | t11 ⇒ t11 | t12 ⇒ t12 | t13 ⇒ t13 | t14 ⇒ t14 | t15 ⇒ t15 | t16 ⇒ t16 | t17 ⇒ t17
  | t18 ⇒ t18 | t19 ⇒ t19 | t1A ⇒ t1A | t1B ⇒ t1B | t1C ⇒ t1C | t1D ⇒ t1D | t1E ⇒ t1E | t1F ⇒ t1F ]
 | t11 ⇒ match e2 with
  [ t00 ⇒ t11 | t01 ⇒ t11 | t02 ⇒ t13 | t03 ⇒ t13 | t04 ⇒ t15 | t05 ⇒ t15 | t06 ⇒ t17 | t07 ⇒ t17
  | t08 ⇒ t19 | t09 ⇒ t19 | t0A ⇒ t1B | t0B ⇒ t1B | t0C ⇒ t1D | t0D ⇒ t1D | t0E ⇒ t1F | t0F ⇒ t1F
  | t10 ⇒ t11 | t11 ⇒ t11 | t12 ⇒ t13 | t13 ⇒ t13 | t14 ⇒ t15 | t15 ⇒ t15 | t16 ⇒ t17 | t17 ⇒ t17
  | t18 ⇒ t19 | t19 ⇒ t19 | t1A ⇒ t1B | t1B ⇒ t1B | t1C ⇒ t1D | t1D ⇒ t1D | t1E ⇒ t1F | t1F ⇒ t1F ]
 | t12 ⇒ match e2 with
  [ t00 ⇒ t12 | t01 ⇒ t13 | t02 ⇒ t12 | t03 ⇒ t13 | t04 ⇒ t16 | t05 ⇒ t17 | t06 ⇒ t16 | t07 ⇒ t17
  | t08 ⇒ t1A | t09 ⇒ t1B | t0A ⇒ t1A | t0B ⇒ t1B | t0C ⇒ t1E | t0D ⇒ t1F | t0E ⇒ t1E | t0F ⇒ t1F
  | t10 ⇒ t12 | t11 ⇒ t13 | t12 ⇒ t12 | t13 ⇒ t13 | t14 ⇒ t16 | t15 ⇒ t17 | t16 ⇒ t16 | t17 ⇒ t17
  | t18 ⇒ t1A | t19 ⇒ t1B | t1A ⇒ t1A | t1B ⇒ t1B | t1C ⇒ t1E | t1D ⇒ t1F | t1E ⇒ t1E | t1F ⇒ t1F ]
 | t13 ⇒ match e2 with
  [ t00 ⇒ t13 | t01 ⇒ t13 | t02 ⇒ t13 | t03 ⇒ t13 | t04 ⇒ t17 | t05 ⇒ t17 | t06 ⇒ t17 | t07 ⇒ t17
  | t08 ⇒ t1B | t09 ⇒ t1B | t0A ⇒ t1B | t0B ⇒ t1B | t0C ⇒ t1F | t0D ⇒ t1F | t0E ⇒ t1F | t0F ⇒ t1F
  | t10 ⇒ t13 | t11 ⇒ t13 | t12 ⇒ t13 | t13 ⇒ t13 | t14 ⇒ t17 | t15 ⇒ t17 | t16 ⇒ t17 | t17 ⇒ t17
  | t18 ⇒ t1B | t19 ⇒ t1B | t1A ⇒ t1B | t1B ⇒ t1B | t1C ⇒ t1F | t1D ⇒ t1F | t1E ⇒ t1F | t1F ⇒ t1F ]
 | t14 ⇒ match e2 with
  [ t00 ⇒ t14 | t01 ⇒ t15 | t02 ⇒ t16 | t03 ⇒ t17 | t04 ⇒ t14 | t05 ⇒ t15 | t06 ⇒ t16 | t07 ⇒ t17
  | t08 ⇒ t1C | t09 ⇒ t1D | t0A ⇒ t1E | t0B ⇒ t1F | t0C ⇒ t1C | t0D ⇒ t1D | t0E ⇒ t1E | t0F ⇒ t1F
  | t10 ⇒ t14 | t11 ⇒ t15 | t12 ⇒ t16 | t13 ⇒ t17 | t14 ⇒ t14 | t15 ⇒ t15 | t16 ⇒ t16 | t17 ⇒ t17
  | t18 ⇒ t1C | t19 ⇒ t1D | t1A ⇒ t1E | t1B ⇒ t1F | t1C ⇒ t1C | t1D ⇒ t1D | t1E ⇒ t1E | t1F ⇒ t1F ]
 | t15 ⇒ match e2 with
  [ t00 ⇒ t15 | t01 ⇒ t15 | t02 ⇒ t17 | t03 ⇒ t17 | t04 ⇒ t15 | t05 ⇒ t15 | t06 ⇒ t17 | t07 ⇒ t17
  | t08 ⇒ t1D | t09 ⇒ t1D | t0A ⇒ t1F | t0B ⇒ t1F | t0C ⇒ t1D | t0D ⇒ t1D | t0E ⇒ t1F | t0F ⇒ t1F
  | t10 ⇒ t15 | t11 ⇒ t15 | t12 ⇒ t17 | t13 ⇒ t17 | t14 ⇒ t15 | t15 ⇒ t15 | t16 ⇒ t17 | t17 ⇒ t17
  | t18 ⇒ t1D | t19 ⇒ t1D | t1A ⇒ t1F | t1B ⇒ t1F | t1C ⇒ t1D | t1D ⇒ t1D | t1E ⇒ t1F | t1F ⇒ t1F ]
 | t16 ⇒ match e2 with
  [ t00 ⇒ t16 | t01 ⇒ t17 | t02 ⇒ t16 | t03 ⇒ t17 | t04 ⇒ t16 | t05 ⇒ t17 | t06 ⇒ t16 | t07 ⇒ t17
  | t08 ⇒ t1E | t09 ⇒ t1F | t0A ⇒ t1E | t0B ⇒ t1F | t0C ⇒ t1E | t0D ⇒ t1F | t0E ⇒ t1E | t0F ⇒ t1F
  | t10 ⇒ t16 | t11 ⇒ t17 | t12 ⇒ t16 | t13 ⇒ t17 | t14 ⇒ t16 | t15 ⇒ t17 | t16 ⇒ t16 | t17 ⇒ t17
  | t18 ⇒ t1E | t19 ⇒ t1F | t1A ⇒ t1E | t1B ⇒ t1F | t1C ⇒ t1E | t1D ⇒ t1F | t1E ⇒ t1E | t1F ⇒ t1F ]
 | t17 ⇒ match e2 with
  [ t00 ⇒ t17 | t01 ⇒ t17 | t02 ⇒ t17 | t03 ⇒ t17 | t04 ⇒ t17 | t05 ⇒ t17 | t06 ⇒ t17 | t07 ⇒ t17
  | t08 ⇒ t1F | t09 ⇒ t1F | t0A ⇒ t1F | t0B ⇒ t1F | t0C ⇒ t1F | t0D ⇒ t1F | t0E ⇒ t1F | t0F ⇒ t1F
  | t10 ⇒ t17 | t11 ⇒ t17 | t12 ⇒ t17 | t13 ⇒ t17 | t14 ⇒ t17 | t15 ⇒ t17 | t16 ⇒ t17 | t17 ⇒ t17
  | t18 ⇒ t1F | t19 ⇒ t1F | t1A ⇒ t1F | t1B ⇒ t1F | t1C ⇒ t1F | t1D ⇒ t1F | t1E ⇒ t1F | t1F ⇒ t1F ]
 | t18 ⇒ match e2 with
  [ t00 ⇒ t18 | t01 ⇒ t19 | t02 ⇒ t1A | t03 ⇒ t1B | t04 ⇒ t1C | t05 ⇒ t1D | t06 ⇒ t1E | t07 ⇒ t1F
  | t08 ⇒ t18 | t09 ⇒ t19 | t0A ⇒ t1A | t0B ⇒ t1B | t0C ⇒ t1C | t0D ⇒ t1D | t0E ⇒ t1E | t0F ⇒ t1F
  | t10 ⇒ t18 | t11 ⇒ t19 | t12 ⇒ t1A | t13 ⇒ t1B | t14 ⇒ t1C | t15 ⇒ t1D | t16 ⇒ t1E | t17 ⇒ t1F
  | t18 ⇒ t18 | t19 ⇒ t19 | t1A ⇒ t1A | t1B ⇒ t1B | t1C ⇒ t1C | t1D ⇒ t1D | t1E ⇒ t1E | t1F ⇒ t1F ]
 | t19 ⇒ match e2 with
  [ t00 ⇒ t19 | t01 ⇒ t19 | t02 ⇒ t1B | t03 ⇒ t1B | t04 ⇒ t1D | t05 ⇒ t1D | t06 ⇒ t1F | t07 ⇒ t1F
  | t08 ⇒ t19 | t09 ⇒ t19 | t0A ⇒ t1B | t0B ⇒ t1B | t0C ⇒ t1D | t0D ⇒ t1D | t0E ⇒ t1F | t0F ⇒ t1F
  | t10 ⇒ t19 | t11 ⇒ t19 | t12 ⇒ t1B | t13 ⇒ t1B | t14 ⇒ t1D | t15 ⇒ t1D | t16 ⇒ t1F | t17 ⇒ t1F
  | t18 ⇒ t19 | t19 ⇒ t19 | t1A ⇒ t1B | t1B ⇒ t1B | t1C ⇒ t1D | t1D ⇒ t1D | t1E ⇒ t1F | t1F ⇒ t1F ]
 | t1A ⇒ match e2 with
  [ t00 ⇒ t1A | t01 ⇒ t1B | t02 ⇒ t1A | t03 ⇒ t1B | t04 ⇒ t1E | t05 ⇒ t1F | t06 ⇒ t1E | t07 ⇒ t1F
  | t08 ⇒ t1A | t09 ⇒ t1B | t0A ⇒ t1A | t0B ⇒ t1B | t0C ⇒ t1E | t0D ⇒ t1F | t0E ⇒ t1E | t0F ⇒ t1F
  | t10 ⇒ t1A | t11 ⇒ t1B | t12 ⇒ t1A | t13 ⇒ t1B | t14 ⇒ t1E | t15 ⇒ t1F | t16 ⇒ t1E | t17 ⇒ t1F
  | t18 ⇒ t1A | t19 ⇒ t1B | t1A ⇒ t1A | t1B ⇒ t1B | t1C ⇒ t1E | t1D ⇒ t1F | t1E ⇒ t1E | t1F ⇒ t1F ]
 | t1B ⇒ match e2 with
  [ t00 ⇒ t1B | t01 ⇒ t1B | t02 ⇒ t1B | t03 ⇒ t1B | t04 ⇒ t1F | t05 ⇒ t1F | t06 ⇒ t1F | t07 ⇒ t1F
  | t08 ⇒ t1B | t09 ⇒ t1B | t0A ⇒ t1B | t0B ⇒ t1B | t0C ⇒ t1F | t0D ⇒ t1F | t0E ⇒ t1F | t0F ⇒ t1F
  | t10 ⇒ t1B | t11 ⇒ t1B | t12 ⇒ t1B | t13 ⇒ t1B | t14 ⇒ t1F | t15 ⇒ t1F | t16 ⇒ t1F | t17 ⇒ t1F
  | t18 ⇒ t1B | t19 ⇒ t1B | t1A ⇒ t1B | t1B ⇒ t1B | t1C ⇒ t1F | t1D ⇒ t1F | t1E ⇒ t1F | t1F ⇒ t1F ]
 | t1C ⇒ match e2 with
  [ t00 ⇒ t1C | t01 ⇒ t1D | t02 ⇒ t1E | t03 ⇒ t1F | t04 ⇒ t1C | t05 ⇒ t1D | t06 ⇒ t1E | t07 ⇒ t1F
  | t08 ⇒ t1C | t09 ⇒ t1D | t0A ⇒ t1E | t0B ⇒ t1F | t0C ⇒ t1C | t0D ⇒ t1D | t0E ⇒ t1E | t0F ⇒ t1F
  | t10 ⇒ t1C | t11 ⇒ t1D | t12 ⇒ t1E | t13 ⇒ t1F | t14 ⇒ t1C | t15 ⇒ t1D | t16 ⇒ t1E | t17 ⇒ t1F
  | t18 ⇒ t1C | t19 ⇒ t1D | t1A ⇒ t1E | t1B ⇒ t1F | t1C ⇒ t1C | t1D ⇒ t1D | t1E ⇒ t1E | t1F ⇒ t1F ]
 | t1D ⇒ match e2 with
  [ t00 ⇒ t1D | t01 ⇒ t1D | t02 ⇒ t1F | t03 ⇒ t1F | t04 ⇒ t1D | t05 ⇒ t1D | t06 ⇒ t1F | t07 ⇒ t1F
  | t08 ⇒ t1D | t09 ⇒ t1D | t0A ⇒ t1F | t0B ⇒ t1F | t0C ⇒ t1D | t0D ⇒ t1D | t0E ⇒ t1F | t0F ⇒ t1F
  | t10 ⇒ t1D | t11 ⇒ t1D | t12 ⇒ t1F | t13 ⇒ t1F | t14 ⇒ t1D | t15 ⇒ t1D | t16 ⇒ t1F | t17 ⇒ t1F
  | t18 ⇒ t1D | t19 ⇒ t1D | t1A ⇒ t1F | t1B ⇒ t1F | t1C ⇒ t1D | t1D ⇒ t1D | t1E ⇒ t1F | t1F ⇒ t1F ]
 | t1E ⇒ match e2 with
  [ t00 ⇒ t1E | t01 ⇒ t1F | t02 ⇒ t1E | t03 ⇒ t1F | t04 ⇒ t1E | t05 ⇒ t1F | t06 ⇒ t1E | t07 ⇒ t1F
  | t08 ⇒ t1E | t09 ⇒ t1F | t0A ⇒ t1E | t0B ⇒ t1F | t0C ⇒ t1E | t0D ⇒ t1F | t0E ⇒ t1E | t0F ⇒ t1F
  | t10 ⇒ t1E | t11 ⇒ t1F | t12 ⇒ t1E | t13 ⇒ t1F | t14 ⇒ t1E | t15 ⇒ t1F | t16 ⇒ t1E | t17 ⇒ t1F
  | t18 ⇒ t1E | t19 ⇒ t1F | t1A ⇒ t1E | t1B ⇒ t1F | t1C ⇒ t1E | t1D ⇒ t1F | t1E ⇒ t1E | t1F ⇒ t1F ]
 | t1F ⇒ match e2 with
  [ t00 ⇒ t1F | t01 ⇒ t1F | t02 ⇒ t1F | t03 ⇒ t1F | t04 ⇒ t1F | t05 ⇒ t1F | t06 ⇒ t1F | t07 ⇒ t1F
  | t08 ⇒ t1F | t09 ⇒ t1F | t0A ⇒ t1F | t0B ⇒ t1F | t0C ⇒ t1F | t0D ⇒ t1F | t0E ⇒ t1F | t0F ⇒ t1F
  | t10 ⇒ t1F | t11 ⇒ t1F | t12 ⇒ t1F | t13 ⇒ t1F | t14 ⇒ t1F | t15 ⇒ t1F | t16 ⇒ t1F | t17 ⇒ t1F
  | t18 ⇒ t1F | t19 ⇒ t1F | t1A ⇒ t1F | t1B ⇒ t1F | t1C ⇒ t1F | t1D ⇒ t1F | t1E ⇒ t1F | t1F ⇒ t1F ]
 ].

(* operatore xor *)
ndefinition xor_bit ≝
λe1,e2.match e1 with
 [ t00 ⇒ match e2 with
  [ t00 ⇒ t00 | t01 ⇒ t01 | t02 ⇒ t02 | t03 ⇒ t03 | t04 ⇒ t04 | t05 ⇒ t05 | t06 ⇒ t06 | t07 ⇒ t07
  | t08 ⇒ t08 | t09 ⇒ t09 | t0A ⇒ t0A | t0B ⇒ t0B | t0C ⇒ t0C | t0D ⇒ t0D | t0E ⇒ t0E | t0F ⇒ t0F
  | t10 ⇒ t10 | t11 ⇒ t11 | t12 ⇒ t12 | t13 ⇒ t13 | t14 ⇒ t14 | t15 ⇒ t15 | t16 ⇒ t16 | t17 ⇒ t17
  | t18 ⇒ t18 | t19 ⇒ t19 | t1A ⇒ t1A | t1B ⇒ t1B | t1C ⇒ t1C | t1D ⇒ t1D | t1E ⇒ t1E | t1F ⇒ t1F ]
 | t01 ⇒ match e2 with
  [ t00 ⇒ t01 | t01 ⇒ t00 | t02 ⇒ t03 | t03 ⇒ t02 | t04 ⇒ t05 | t05 ⇒ t04 | t06 ⇒ t07 | t07 ⇒ t06
  | t08 ⇒ t09 | t09 ⇒ t08 | t0A ⇒ t0B | t0B ⇒ t0A | t0C ⇒ t0D | t0D ⇒ t0C | t0E ⇒ t0F | t0F ⇒ t0E
  | t10 ⇒ t11 | t11 ⇒ t10 | t12 ⇒ t13 | t13 ⇒ t12 | t14 ⇒ t15 | t15 ⇒ t14 | t16 ⇒ t17 | t17 ⇒ t16
  | t18 ⇒ t19 | t19 ⇒ t18 | t1A ⇒ t1B | t1B ⇒ t1A | t1C ⇒ t1D | t1D ⇒ t1C | t1E ⇒ t1F | t1F ⇒ t1E ]
 | t02 ⇒ match e2 with
  [ t00 ⇒ t02 | t01 ⇒ t03 | t02 ⇒ t00 | t03 ⇒ t01 | t04 ⇒ t06 | t05 ⇒ t07 | t06 ⇒ t04 | t07 ⇒ t05
  | t08 ⇒ t0A | t09 ⇒ t0B | t0A ⇒ t08 | t0B ⇒ t09 | t0C ⇒ t0E | t0D ⇒ t0F | t0E ⇒ t0C | t0F ⇒ t0D
  | t10 ⇒ t12 | t11 ⇒ t13 | t12 ⇒ t10 | t13 ⇒ t11 | t14 ⇒ t16 | t15 ⇒ t17 | t16 ⇒ t14 | t17 ⇒ t15
  | t18 ⇒ t1A | t19 ⇒ t1B | t1A ⇒ t18 | t1B ⇒ t19 | t1C ⇒ t1E | t1D ⇒ t1F | t1E ⇒ t1C | t1F ⇒ t1D ]
 | t03 ⇒ match e2 with
  [ t00 ⇒ t03 | t01 ⇒ t02 | t02 ⇒ t01 | t03 ⇒ t00 | t04 ⇒ t07 | t05 ⇒ t06 | t06 ⇒ t05 | t07 ⇒ t04
  | t08 ⇒ t0B | t09 ⇒ t0A | t0A ⇒ t09 | t0B ⇒ t08 | t0C ⇒ t0F | t0D ⇒ t0E | t0E ⇒ t0D | t0F ⇒ t0C
  | t10 ⇒ t13 | t11 ⇒ t12 | t12 ⇒ t11 | t13 ⇒ t10 | t14 ⇒ t17 | t15 ⇒ t16 | t16 ⇒ t15 | t17 ⇒ t14
  | t18 ⇒ t1B | t19 ⇒ t1A | t1A ⇒ t19 | t1B ⇒ t18 | t1C ⇒ t1F | t1D ⇒ t1E | t1E ⇒ t1D | t1F ⇒ t1C ]
 | t04 ⇒ match e2 with
  [ t00 ⇒ t04 | t01 ⇒ t05 | t02 ⇒ t06 | t03 ⇒ t07 | t04 ⇒ t00 | t05 ⇒ t01 | t06 ⇒ t02 | t07 ⇒ t03
  | t08 ⇒ t0C | t09 ⇒ t0D | t0A ⇒ t0E | t0B ⇒ t0F | t0C ⇒ t08 | t0D ⇒ t09 | t0E ⇒ t0A | t0F ⇒ t0B
  | t10 ⇒ t14 | t11 ⇒ t15 | t12 ⇒ t16 | t13 ⇒ t17 | t14 ⇒ t10 | t15 ⇒ t11 | t16 ⇒ t12 | t17 ⇒ t13
  | t18 ⇒ t1C | t19 ⇒ t1D | t1A ⇒ t1E | t1B ⇒ t1F | t1C ⇒ t18 | t1D ⇒ t19 | t1E ⇒ t1A | t1F ⇒ t1B ]
 | t05 ⇒ match e2 with
  [ t00 ⇒ t05 | t01 ⇒ t04 | t02 ⇒ t07 | t03 ⇒ t06 | t04 ⇒ t01 | t05 ⇒ t00 | t06 ⇒ t03 | t07 ⇒ t02
  | t08 ⇒ t0D | t09 ⇒ t0C | t0A ⇒ t0F | t0B ⇒ t0E | t0C ⇒ t09 | t0D ⇒ t08 | t0E ⇒ t0B | t0F ⇒ t0A
  | t10 ⇒ t15 | t11 ⇒ t14 | t12 ⇒ t17 | t13 ⇒ t16 | t14 ⇒ t11 | t15 ⇒ t10 | t16 ⇒ t13 | t17 ⇒ t12
  | t18 ⇒ t1D | t19 ⇒ t1C | t1A ⇒ t1F | t1B ⇒ t1E | t1C ⇒ t19 | t1D ⇒ t18 | t1E ⇒ t1B | t1F ⇒ t1A ]
 | t06 ⇒ match e2 with
  [ t00 ⇒ t06 | t01 ⇒ t07 | t02 ⇒ t04 | t03 ⇒ t05 | t04 ⇒ t02 | t05 ⇒ t03 | t06 ⇒ t00 | t07 ⇒ t01
  | t08 ⇒ t0E | t09 ⇒ t0F | t0A ⇒ t0C | t0B ⇒ t0D | t0C ⇒ t0A | t0D ⇒ t0B | t0E ⇒ t08 | t0F ⇒ t09
  | t10 ⇒ t16 | t11 ⇒ t17 | t12 ⇒ t14 | t13 ⇒ t15 | t14 ⇒ t12 | t15 ⇒ t13 | t16 ⇒ t10 | t17 ⇒ t11
  | t18 ⇒ t1E | t19 ⇒ t1F | t1A ⇒ t1C | t1B ⇒ t1D | t1C ⇒ t1A | t1D ⇒ t1B | t1E ⇒ t18 | t1F ⇒ t19 ]
 | t07 ⇒ match e2 with
  [ t00 ⇒ t07 | t01 ⇒ t06 | t02 ⇒ t05 | t03 ⇒ t04 | t04 ⇒ t03 | t05 ⇒ t02 | t06 ⇒ t01 | t07 ⇒ t00
  | t08 ⇒ t0F | t09 ⇒ t0E | t0A ⇒ t0D | t0B ⇒ t0C | t0C ⇒ t0B | t0D ⇒ t0A | t0E ⇒ t09 | t0F ⇒ t08
  | t10 ⇒ t17 | t11 ⇒ t16 | t12 ⇒ t15 | t13 ⇒ t14 | t14 ⇒ t13 | t15 ⇒ t12 | t16 ⇒ t11 | t17 ⇒ t10
  | t18 ⇒ t1F | t19 ⇒ t1E | t1A ⇒ t1D | t1B ⇒ t1C | t1C ⇒ t1B | t1D ⇒ t1A | t1E ⇒ t19 | t1F ⇒ t18 ]
 | t08 ⇒ match e2 with
  [ t00 ⇒ t08 | t01 ⇒ t09 | t02 ⇒ t0A | t03 ⇒ t0B | t04 ⇒ t0C | t05 ⇒ t0D | t06 ⇒ t0E | t07 ⇒ t0F
  | t08 ⇒ t00 | t09 ⇒ t01 | t0A ⇒ t02 | t0B ⇒ t03 | t0C ⇒ t04 | t0D ⇒ t05 | t0E ⇒ t06 | t0F ⇒ t07
  | t10 ⇒ t18 | t11 ⇒ t19 | t12 ⇒ t1A | t13 ⇒ t1B | t14 ⇒ t1C | t15 ⇒ t1D | t16 ⇒ t1E | t17 ⇒ t1F
  | t18 ⇒ t10 | t19 ⇒ t11 | t1A ⇒ t12 | t1B ⇒ t13 | t1C ⇒ t14 | t1D ⇒ t15 | t1E ⇒ t16 | t1F ⇒ t17 ]
 | t09 ⇒ match e2 with
  [ t00 ⇒ t09 | t01 ⇒ t08 | t02 ⇒ t0B | t03 ⇒ t0A | t04 ⇒ t0D | t05 ⇒ t0C | t06 ⇒ t0F | t07 ⇒ t0E
  | t08 ⇒ t01 | t09 ⇒ t00 | t0A ⇒ t03 | t0B ⇒ t02 | t0C ⇒ t05 | t0D ⇒ t04 | t0E ⇒ t07 | t0F ⇒ t06
  | t10 ⇒ t19 | t11 ⇒ t18 | t12 ⇒ t1B | t13 ⇒ t1A | t14 ⇒ t1D | t15 ⇒ t1C | t16 ⇒ t1F | t17 ⇒ t1E
  | t18 ⇒ t11 | t19 ⇒ t10 | t1A ⇒ t13 | t1B ⇒ t12 | t1C ⇒ t15 | t1D ⇒ t14 | t1E ⇒ t17 | t1F ⇒ t16 ]
 | t0A ⇒ match e2 with
  [ t00 ⇒ t0A | t01 ⇒ t0B | t02 ⇒ t08 | t03 ⇒ t09 | t04 ⇒ t0E | t05 ⇒ t0F | t06 ⇒ t0C | t07 ⇒ t0D
  | t08 ⇒ t02 | t09 ⇒ t03 | t0A ⇒ t00 | t0B ⇒ t01 | t0C ⇒ t06 | t0D ⇒ t07 | t0E ⇒ t04 | t0F ⇒ t05
  | t10 ⇒ t1A | t11 ⇒ t1B | t12 ⇒ t18 | t13 ⇒ t19 | t14 ⇒ t1E | t15 ⇒ t1F | t16 ⇒ t1C | t17 ⇒ t1D
  | t18 ⇒ t12 | t19 ⇒ t13 | t1A ⇒ t10 | t1B ⇒ t11 | t1C ⇒ t16 | t1D ⇒ t17 | t1E ⇒ t14 | t1F ⇒ t15 ]
 | t0B ⇒ match e2 with
  [ t00 ⇒ t0B | t01 ⇒ t0A | t02 ⇒ t09 | t03 ⇒ t08 | t04 ⇒ t0F | t05 ⇒ t0E | t06 ⇒ t0D | t07 ⇒ t0C
  | t08 ⇒ t03 | t09 ⇒ t02 | t0A ⇒ t01 | t0B ⇒ t00 | t0C ⇒ t07 | t0D ⇒ t06 | t0E ⇒ t05 | t0F ⇒ t04
  | t10 ⇒ t1B | t11 ⇒ t1A | t12 ⇒ t19 | t13 ⇒ t18 | t14 ⇒ t1F | t15 ⇒ t1E | t16 ⇒ t1D | t17 ⇒ t1C
  | t18 ⇒ t13 | t19 ⇒ t12 | t1A ⇒ t11 | t1B ⇒ t10 | t1C ⇒ t17 | t1D ⇒ t16 | t1E ⇒ t15 | t1F ⇒ t14 ]
 | t0C ⇒ match e2 with
  [ t00 ⇒ t0C | t01 ⇒ t0D | t02 ⇒ t0E | t03 ⇒ t0F | t04 ⇒ t08 | t05 ⇒ t09 | t06 ⇒ t0A | t07 ⇒ t0B
  | t08 ⇒ t04 | t09 ⇒ t05 | t0A ⇒ t06 | t0B ⇒ t07 | t0C ⇒ t00 | t0D ⇒ t01 | t0E ⇒ t02 | t0F ⇒ t03
  | t10 ⇒ t1C | t11 ⇒ t1D | t12 ⇒ t1E | t13 ⇒ t1F | t14 ⇒ t18 | t15 ⇒ t19 | t16 ⇒ t1A | t17 ⇒ t1B
  | t18 ⇒ t14 | t19 ⇒ t15 | t1A ⇒ t16 | t1B ⇒ t17 | t1C ⇒ t10 | t1D ⇒ t11 | t1E ⇒ t12 | t1F ⇒ t13 ]
 | t0D ⇒ match e2 with
  [ t00 ⇒ t0D | t01 ⇒ t0C | t02 ⇒ t0F | t03 ⇒ t0E | t04 ⇒ t09 | t05 ⇒ t08 | t06 ⇒ t0B | t07 ⇒ t0A
  | t08 ⇒ t05 | t09 ⇒ t04 | t0A ⇒ t07 | t0B ⇒ t06 | t0C ⇒ t01 | t0D ⇒ t00 | t0E ⇒ t03 | t0F ⇒ t02
  | t10 ⇒ t1D | t11 ⇒ t1C | t12 ⇒ t1F | t13 ⇒ t1E | t14 ⇒ t19 | t15 ⇒ t18 | t16 ⇒ t1B | t17 ⇒ t1A
  | t18 ⇒ t15 | t19 ⇒ t14 | t1A ⇒ t17 | t1B ⇒ t16 | t1C ⇒ t11 | t1D ⇒ t10 | t1E ⇒ t13 | t1F ⇒ t12 ]
 | t0E ⇒ match e2 with
  [ t00 ⇒ t0E | t01 ⇒ t0F | t02 ⇒ t0C | t03 ⇒ t0D | t04 ⇒ t0A | t05 ⇒ t0B | t06 ⇒ t08 | t07 ⇒ t09
  | t08 ⇒ t06 | t09 ⇒ t07 | t0A ⇒ t04 | t0B ⇒ t05 | t0C ⇒ t02 | t0D ⇒ t03 | t0E ⇒ t00 | t0F ⇒ t01
  | t10 ⇒ t1E | t11 ⇒ t1F | t12 ⇒ t1C | t13 ⇒ t1D | t14 ⇒ t1A | t15 ⇒ t1B | t16 ⇒ t18 | t17 ⇒ t19
  | t18 ⇒ t16 | t19 ⇒ t17 | t1A ⇒ t14 | t1B ⇒ t15 | t1C ⇒ t12 | t1D ⇒ t13 | t1E ⇒ t10 | t1F ⇒ t11 ]
 | t0F ⇒ match e2 with
  [ t00 ⇒ t0F | t01 ⇒ t0E | t02 ⇒ t0D | t03 ⇒ t0C | t04 ⇒ t0B | t05 ⇒ t0A | t06 ⇒ t09 | t07 ⇒ t08
  | t08 ⇒ t07 | t09 ⇒ t06 | t0A ⇒ t05 | t0B ⇒ t04 | t0C ⇒ t03 | t0D ⇒ t02 | t0E ⇒ t01 | t0F ⇒ t00
  | t10 ⇒ t1F | t11 ⇒ t1E | t12 ⇒ t1D | t13 ⇒ t1C | t14 ⇒ t1B | t15 ⇒ t1A | t16 ⇒ t19 | t17 ⇒ t18
  | t18 ⇒ t17 | t19 ⇒ t16 | t1A ⇒ t15 | t1B ⇒ t14 | t1C ⇒ t13 | t1D ⇒ t12 | t1E ⇒ t11 | t1F ⇒ t10 ]
 | t10 ⇒ match e2 with
  [ t00 ⇒ t10 | t01 ⇒ t11 | t02 ⇒ t12 | t03 ⇒ t13 | t04 ⇒ t14 | t05 ⇒ t15 | t06 ⇒ t16 | t07 ⇒ t17
  | t08 ⇒ t18 | t09 ⇒ t19 | t0A ⇒ t1A | t0B ⇒ t1B | t0C ⇒ t1C | t0D ⇒ t1D | t0E ⇒ t1E | t0F ⇒ t1F
  | t10 ⇒ t00 | t11 ⇒ t01 | t12 ⇒ t02 | t13 ⇒ t03 | t14 ⇒ t04 | t15 ⇒ t05 | t16 ⇒ t06 | t17 ⇒ t07
  | t18 ⇒ t08 | t19 ⇒ t09 | t1A ⇒ t0A | t1B ⇒ t0B | t1C ⇒ t0C | t1D ⇒ t0D | t1E ⇒ t0E | t1F ⇒ t0F ]
 | t11 ⇒ match e2 with
  [ t00 ⇒ t11 | t01 ⇒ t10 | t02 ⇒ t13 | t03 ⇒ t12 | t04 ⇒ t15 | t05 ⇒ t14 | t06 ⇒ t17 | t07 ⇒ t16
  | t08 ⇒ t19 | t09 ⇒ t18 | t0A ⇒ t1B | t0B ⇒ t1A | t0C ⇒ t1D | t0D ⇒ t1C | t0E ⇒ t1F | t0F ⇒ t1E
  | t10 ⇒ t01 | t11 ⇒ t00 | t12 ⇒ t03 | t13 ⇒ t02 | t14 ⇒ t05 | t15 ⇒ t04 | t16 ⇒ t07 | t17 ⇒ t06
  | t18 ⇒ t09 | t19 ⇒ t08 | t1A ⇒ t0B | t1B ⇒ t0A | t1C ⇒ t0D | t1D ⇒ t0C | t1E ⇒ t0F | t1F ⇒ t0E ]
 | t12 ⇒ match e2 with
  [ t00 ⇒ t12 | t01 ⇒ t13 | t02 ⇒ t10 | t03 ⇒ t11 | t04 ⇒ t16 | t05 ⇒ t17 | t06 ⇒ t14 | t07 ⇒ t15
  | t08 ⇒ t1A | t09 ⇒ t1B | t0A ⇒ t18 | t0B ⇒ t19 | t0C ⇒ t1E | t0D ⇒ t1F | t0E ⇒ t1C | t0F ⇒ t1D
  | t10 ⇒ t02 | t11 ⇒ t03 | t12 ⇒ t00 | t13 ⇒ t01 | t14 ⇒ t06 | t15 ⇒ t07 | t16 ⇒ t04 | t17 ⇒ t05
  | t18 ⇒ t0A | t19 ⇒ t0B | t1A ⇒ t08 | t1B ⇒ t09 | t1C ⇒ t0E | t1D ⇒ t0F | t1E ⇒ t0C | t1F ⇒ t0D ]
 | t13 ⇒ match e2 with
  [ t00 ⇒ t13 | t01 ⇒ t12 | t02 ⇒ t11 | t03 ⇒ t10 | t04 ⇒ t17 | t05 ⇒ t16 | t06 ⇒ t15 | t07 ⇒ t14
  | t08 ⇒ t1B | t09 ⇒ t1A | t0A ⇒ t19 | t0B ⇒ t18 | t0C ⇒ t1F | t0D ⇒ t1E | t0E ⇒ t1D | t0F ⇒ t1C
  | t10 ⇒ t03 | t11 ⇒ t02 | t12 ⇒ t01 | t13 ⇒ t00 | t14 ⇒ t07 | t15 ⇒ t06 | t16 ⇒ t05 | t17 ⇒ t04
  | t18 ⇒ t0B | t19 ⇒ t0A | t1A ⇒ t09 | t1B ⇒ t08 | t1C ⇒ t0F | t1D ⇒ t0E | t1E ⇒ t0D | t1F ⇒ t0C ]
 | t14 ⇒ match e2 with
  [ t00 ⇒ t14 | t01 ⇒ t15 | t02 ⇒ t16 | t03 ⇒ t17 | t04 ⇒ t10 | t05 ⇒ t11 | t06 ⇒ t12 | t07 ⇒ t13
  | t08 ⇒ t1C | t09 ⇒ t1D | t0A ⇒ t1E | t0B ⇒ t1F | t0C ⇒ t18 | t0D ⇒ t19 | t0E ⇒ t1A | t0F ⇒ t1B
  | t10 ⇒ t04 | t11 ⇒ t05 | t12 ⇒ t06 | t13 ⇒ t07 | t14 ⇒ t00 | t15 ⇒ t01 | t16 ⇒ t02 | t17 ⇒ t03
  | t18 ⇒ t0C | t19 ⇒ t0D | t1A ⇒ t0E | t1B ⇒ t0F | t1C ⇒ t08 | t1D ⇒ t09 | t1E ⇒ t0A | t1F ⇒ t0B ]
 | t15 ⇒ match e2 with
  [ t00 ⇒ t15 | t01 ⇒ t14 | t02 ⇒ t17 | t03 ⇒ t16 | t04 ⇒ t11 | t05 ⇒ t10 | t06 ⇒ t13 | t07 ⇒ t12
  | t08 ⇒ t1D | t09 ⇒ t1C | t0A ⇒ t1F | t0B ⇒ t1E | t0C ⇒ t19 | t0D ⇒ t18 | t0E ⇒ t1B | t0F ⇒ t1A
  | t10 ⇒ t05 | t11 ⇒ t04 | t12 ⇒ t07 | t13 ⇒ t06 | t14 ⇒ t01 | t15 ⇒ t00 | t16 ⇒ t03 | t17 ⇒ t02
  | t18 ⇒ t0D | t19 ⇒ t0C | t1A ⇒ t0F | t1B ⇒ t0E | t1C ⇒ t09 | t1D ⇒ t08 | t1E ⇒ t0B | t1F ⇒ t0A ]
 | t16 ⇒ match e2 with
  [ t00 ⇒ t16 | t01 ⇒ t17 | t02 ⇒ t14 | t03 ⇒ t15 | t04 ⇒ t12 | t05 ⇒ t13 | t06 ⇒ t10 | t07 ⇒ t11
  | t08 ⇒ t1E | t09 ⇒ t1F | t0A ⇒ t1C | t0B ⇒ t1D | t0C ⇒ t1A | t0D ⇒ t1B | t0E ⇒ t18 | t0F ⇒ t19
  | t10 ⇒ t06 | t11 ⇒ t07 | t12 ⇒ t04 | t13 ⇒ t05 | t14 ⇒ t02 | t15 ⇒ t03 | t16 ⇒ t00 | t17 ⇒ t01
  | t18 ⇒ t0E | t19 ⇒ t0F | t1A ⇒ t0C | t1B ⇒ t0D | t1C ⇒ t0A | t1D ⇒ t0B | t1E ⇒ t08 | t1F ⇒ t09 ]
 | t17 ⇒ match e2 with
  [ t00 ⇒ t17 | t01 ⇒ t16 | t02 ⇒ t15 | t03 ⇒ t14 | t04 ⇒ t13 | t05 ⇒ t12 | t06 ⇒ t11 | t07 ⇒ t10
  | t08 ⇒ t1F | t09 ⇒ t1E | t0A ⇒ t1D | t0B ⇒ t1C | t0C ⇒ t1B | t0D ⇒ t1A | t0E ⇒ t19 | t0F ⇒ t18
  | t10 ⇒ t07 | t11 ⇒ t06 | t12 ⇒ t05 | t13 ⇒ t04 | t14 ⇒ t03 | t15 ⇒ t02 | t16 ⇒ t01 | t17 ⇒ t00
  | t18 ⇒ t0F | t19 ⇒ t0E | t1A ⇒ t0D | t1B ⇒ t0C | t1C ⇒ t0B | t1D ⇒ t0A | t1E ⇒ t09 | t1F ⇒ t08 ]
 | t18 ⇒ match e2 with
  [ t00 ⇒ t18 | t01 ⇒ t19 | t02 ⇒ t1A | t03 ⇒ t1B | t04 ⇒ t1C | t05 ⇒ t1D | t06 ⇒ t1E | t07 ⇒ t1F
  | t08 ⇒ t10 | t09 ⇒ t11 | t0A ⇒ t12 | t0B ⇒ t13 | t0C ⇒ t14 | t0D ⇒ t15 | t0E ⇒ t16 | t0F ⇒ t17
  | t10 ⇒ t08 | t11 ⇒ t09 | t12 ⇒ t0A | t13 ⇒ t0B | t14 ⇒ t0C | t15 ⇒ t0D | t16 ⇒ t0E | t17 ⇒ t0F
  | t18 ⇒ t00 | t19 ⇒ t01 | t1A ⇒ t02 | t1B ⇒ t03 | t1C ⇒ t04 | t1D ⇒ t05 | t1E ⇒ t06 | t1F ⇒ t07 ]
 | t19 ⇒ match e2 with
  [ t00 ⇒ t19 | t01 ⇒ t18 | t02 ⇒ t1B | t03 ⇒ t1A | t04 ⇒ t1D | t05 ⇒ t1C | t06 ⇒ t1F | t07 ⇒ t1E
  | t08 ⇒ t11 | t09 ⇒ t10 | t0A ⇒ t13 | t0B ⇒ t12 | t0C ⇒ t15 | t0D ⇒ t14 | t0E ⇒ t17 | t0F ⇒ t16
  | t10 ⇒ t09 | t11 ⇒ t08 | t12 ⇒ t0B | t13 ⇒ t0A | t14 ⇒ t0D | t15 ⇒ t0C | t16 ⇒ t0F | t17 ⇒ t0E
  | t18 ⇒ t01 | t19 ⇒ t00 | t1A ⇒ t03 | t1B ⇒ t02 | t1C ⇒ t05 | t1D ⇒ t04 | t1E ⇒ t07 | t1F ⇒ t06 ]
 | t1A ⇒ match e2 with
  [ t00 ⇒ t1A | t01 ⇒ t1B | t02 ⇒ t18 | t03 ⇒ t19 | t04 ⇒ t1E | t05 ⇒ t1F | t06 ⇒ t1C | t07 ⇒ t1D
  | t08 ⇒ t12 | t09 ⇒ t13 | t0A ⇒ t10 | t0B ⇒ t11 | t0C ⇒ t16 | t0D ⇒ t17 | t0E ⇒ t14 | t0F ⇒ t15
  | t10 ⇒ t0A | t11 ⇒ t0B | t12 ⇒ t08 | t13 ⇒ t09 | t14 ⇒ t0E | t15 ⇒ t0F | t16 ⇒ t0C | t17 ⇒ t0D
  | t18 ⇒ t02 | t19 ⇒ t03 | t1A ⇒ t00 | t1B ⇒ t01 | t1C ⇒ t06 | t1D ⇒ t07 | t1E ⇒ t04 | t1F ⇒ t05 ]
 | t1B ⇒ match e2 with
  [ t00 ⇒ t1B | t01 ⇒ t1A | t02 ⇒ t19 | t03 ⇒ t18 | t04 ⇒ t1F | t05 ⇒ t1E | t06 ⇒ t1D | t07 ⇒ t1C
  | t08 ⇒ t13 | t09 ⇒ t12 | t0A ⇒ t11 | t0B ⇒ t10 | t0C ⇒ t17 | t0D ⇒ t16 | t0E ⇒ t15 | t0F ⇒ t14
  | t10 ⇒ t0B | t11 ⇒ t0A | t12 ⇒ t09 | t13 ⇒ t08 | t14 ⇒ t0F | t15 ⇒ t0E | t16 ⇒ t0D | t17 ⇒ t0C
  | t18 ⇒ t03 | t19 ⇒ t02 | t1A ⇒ t01 | t1B ⇒ t00 | t1C ⇒ t07 | t1D ⇒ t06 | t1E ⇒ t05 | t1F ⇒ t04 ]
 | t1C ⇒ match e2 with
  [ t00 ⇒ t1C | t01 ⇒ t1D | t02 ⇒ t1E | t03 ⇒ t1F | t04 ⇒ t18 | t05 ⇒ t19 | t06 ⇒ t1A | t07 ⇒ t1B
  | t08 ⇒ t14 | t09 ⇒ t15 | t0A ⇒ t16 | t0B ⇒ t17 | t0C ⇒ t10 | t0D ⇒ t11 | t0E ⇒ t12 | t0F ⇒ t13
  | t10 ⇒ t0C | t11 ⇒ t0D | t12 ⇒ t0E | t13 ⇒ t0F | t14 ⇒ t08 | t15 ⇒ t09 | t16 ⇒ t0A | t17 ⇒ t0B
  | t18 ⇒ t04 | t19 ⇒ t05 | t1A ⇒ t06 | t1B ⇒ t07 | t1C ⇒ t00 | t1D ⇒ t01 | t1E ⇒ t02 | t1F ⇒ t03 ]
 | t1D ⇒ match e2 with
  [ t00 ⇒ t1D | t01 ⇒ t1C | t02 ⇒ t1F | t03 ⇒ t1E | t04 ⇒ t19 | t05 ⇒ t18 | t06 ⇒ t1B | t07 ⇒ t1A
  | t08 ⇒ t15 | t09 ⇒ t14 | t0A ⇒ t17 | t0B ⇒ t16 | t0C ⇒ t11 | t0D ⇒ t10 | t0E ⇒ t13 | t0F ⇒ t12
  | t10 ⇒ t0D | t11 ⇒ t0C | t12 ⇒ t0F | t13 ⇒ t0E | t14 ⇒ t09 | t15 ⇒ t08 | t16 ⇒ t0B | t17 ⇒ t0A
  | t18 ⇒ t05 | t19 ⇒ t04 | t1A ⇒ t07 | t1B ⇒ t06 | t1C ⇒ t01 | t1D ⇒ t00 | t1E ⇒ t03 | t1F ⇒ t02 ]
 | t1E ⇒ match e2 with
  [ t00 ⇒ t1E | t01 ⇒ t1F | t02 ⇒ t1C | t03 ⇒ t1D | t04 ⇒ t1A | t05 ⇒ t1B | t06 ⇒ t18 | t07 ⇒ t19
  | t08 ⇒ t16 | t09 ⇒ t17 | t0A ⇒ t14 | t0B ⇒ t15 | t0C ⇒ t12 | t0D ⇒ t13 | t0E ⇒ t10 | t0F ⇒ t11
  | t10 ⇒ t0E | t11 ⇒ t0F | t12 ⇒ t0C | t13 ⇒ t0D | t14 ⇒ t0A | t15 ⇒ t0B | t16 ⇒ t08 | t17 ⇒ t09
  | t18 ⇒ t06 | t19 ⇒ t07 | t1A ⇒ t04 | t1B ⇒ t05 | t1C ⇒ t02 | t1D ⇒ t03 | t1E ⇒ t00 | t1F ⇒ t01 ]
 | t1F ⇒ match e2 with
  [ t00 ⇒ t1F | t01 ⇒ t1E | t02 ⇒ t1D | t03 ⇒ t1C | t04 ⇒ t1B | t05 ⇒ t1A | t06 ⇒ t19 | t07 ⇒ t18
  | t08 ⇒ t17 | t09 ⇒ t16 | t0A ⇒ t15 | t0B ⇒ t14 | t0C ⇒ t13 | t0D ⇒ t12 | t0E ⇒ t11 | t0F ⇒ t10
  | t10 ⇒ t0F | t11 ⇒ t0E | t12 ⇒ t0D | t13 ⇒ t0C | t14 ⇒ t0B | t15 ⇒ t0A | t16 ⇒ t09 | t17 ⇒ t08
  | t18 ⇒ t07 | t19 ⇒ t06 | t1A ⇒ t05 | t1B ⇒ t04 | t1C ⇒ t03 | t1D ⇒ t02 | t1E ⇒ t01 | t1F ⇒ t00 ]
 ].

(* operatore predecessore *)
ndefinition pred_bit ≝
λn.match n with
 [ t00 ⇒ t1F | t01 ⇒ t00 | t02 ⇒ t01 | t03 ⇒ t02 | t04 ⇒ t03 | t05 ⇒ t04 | t06 ⇒ t05 | t07 ⇒ t06
 | t08 ⇒ t07 | t09 ⇒ t08 | t0A ⇒ t09 | t0B ⇒ t0A | t0C ⇒ t0B | t0D ⇒ t0C | t0E ⇒ t0D | t0F ⇒ t0E
 | t10 ⇒ t0F | t11 ⇒ t10 | t12 ⇒ t11 | t13 ⇒ t12 | t14 ⇒ t13 | t15 ⇒ t14 | t16 ⇒ t15 | t17 ⇒ t16
 | t18 ⇒ t17 | t19 ⇒ t18 | t1A ⇒ t19 | t1B ⇒ t1A | t1C ⇒ t1B | t1D ⇒ t1C | t1E ⇒ t1D | t1F ⇒ t0E
 ].

(* operatore successore *)
ndefinition succ_bit ≝
λn.match n with
 [ t00 ⇒ t01 | t01 ⇒ t02 | t02 ⇒ t03 | t03 ⇒ t04 | t04 ⇒ t05 | t05 ⇒ t06 | t06 ⇒ t07 | t07 ⇒ t08
 | t08 ⇒ t09 | t09 ⇒ t0A | t0A ⇒ t0B | t0B ⇒ t0C | t0C ⇒ t0D | t0D ⇒ t0E | t0E ⇒ t0F | t0F ⇒ t10
 | t10 ⇒ t11 | t11 ⇒ t12 | t12 ⇒ t13 | t13 ⇒ t14 | t14 ⇒ t15 | t15 ⇒ t16 | t16 ⇒ t17 | t17 ⇒ t18
 | t18 ⇒ t19 | t19 ⇒ t1A | t1A ⇒ t1B | t1B ⇒ t1C | t1C ⇒ t1D | t1D ⇒ t1E | t1E ⇒ t1F | t1F ⇒ t00
 ].

(* bitrigesimali ricorsivi *)
ninductive rec_bitrigesim : bitrigesim → Type ≝
  bi_O : rec_bitrigesim t00
| bi_S : ∀n.rec_bitrigesim n → rec_bitrigesim (succ_bit n).

(* bitrigesimali → bitrigesimali ricorsivi *)
ndefinition bit_to_recbit ≝
λn.match n return λx.rec_bitrigesim x with
 [ t00 ⇒ bi_O
 | t01 ⇒ bi_S ? bi_O
 | t02 ⇒ bi_S ? (bi_S ? bi_O)
 | t03 ⇒ bi_S ? (bi_S ? (bi_S ? bi_O))
 | t04 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O)))
 | t05 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O))))
 | t06 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O)))))
 | t07 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O))))))
 | t08 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
         bi_O)))))))
 | t09 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? bi_O))))))))
 | t0A ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? bi_O)))))))))
 | t0B ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? bi_O))))))))))
 | t0C ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O)))))))))))
 | t0D ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O))))))))))))
 | t0E ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O)))))))))))))
 | t0F ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O))))))))))))))
 | t10 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
         bi_O)))))))))))))))
 | t11 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? bi_O))))))))))))))))
 | t12 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? bi_O)))))))))))))))))
 | t13 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? bi_O))))))))))))))))))
 | t14 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O)))))))))))))))))))
 | t15 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O))))))))))))))))))))
 | t16 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O)))))))))))))))))))))
 | t17 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O))))))))))))))))))))))
 | t18 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
         bi_O)))))))))))))))))))))))
 | t19 ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? bi_O))))))))))))))))))))))))
 | t1A ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? bi_O)))))))))))))))))))))))))
 | t1B ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? bi_O))))))))))))))))))))))))))
 | t1C ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O)))))))))))))))))))))))))))
 | t1D ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O))))))))))))))))))))))))))))
 | t1E ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O)))))))))))))))))))))))))))))
 | t1F ⇒ bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ?
        (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? (bi_S ? bi_O))))))))))))))))))))))))))))))
 ].

ndefinition bitrigesim_destruct_aux ≝
Πt1,t2:bitrigesim.ΠP:Prop.t1 = t2 →
 match eq_bit t1 t2 with [ true ⇒ P → P | false ⇒ P ].

ndefinition bitrigesim_destruct : bitrigesim_destruct_aux.
 #t1; #t2; #P; #H;
 nrewrite < H;
 nelim t1;
 nnormalize;
 napply (λx.x).
nqed.

nlemma eq_to_eqbit : ∀n1,n2.n1 = n2 → eq_bit n1 n2 = true.
 #n1; #n2; #H;
 nrewrite > H;
 nelim n2;
 nnormalize;
 napply refl_eq.
nqed.

nlemma neqbit_to_neq : ∀n1,n2.eq_bit n1 n2 = false → n1 ≠ n2.
 #n1; #n2; #H;
 napply (not_to_not (n1 = n2) (eq_bit n1 n2 = true) …);
 ##[ ##1: napply (eq_to_eqbit n1 n2)
 ##| ##2: napply (eqfalse_to_neqtrue … H)
 ##]
nqed.

(* !!! per brevita... *)
naxiom eqbit_to_eq : ∀t1,t2.eq_bit t1 t2 = true → t1 = t2.

nlemma neq_to_neqbit : ∀n1,n2.n1 ≠ n2 → eq_bit n1 n2 = false.
 #n1; #n2; #H;
 napply (neqtrue_to_eqfalse (eq_bit n1 n2));
 napply (not_to_not (eq_bit n1 n2 = true) (n1 = n2) ? H);
 napply (eqbit_to_eq n1 n2).
nqed.

nlemma decidable_bit : ∀x,y:bitrigesim.decidable (x = y).
 #x; #y; nnormalize;
 napply (or2_elim (eq_bit x y = true) (eq_bit x y = false) ? (decidable_bexpr ?));
 ##[ ##1: #H; napply (or2_intro1 (x = y) (x ≠ y) (eqbit_to_eq … H))
 ##| ##2: #H; napply (or2_intro2 (x = y) (x ≠ y) (neqbit_to_neq … H))
 ##]
nqed.

nlemma symmetric_eqbit : symmetricT bitrigesim bool eq_bit.
 #n1; #n2;
 napply (or2_elim (n1 = n2) (n1 ≠ n2) ? (decidable_bit n1 n2));
 ##[ ##1: #H; nrewrite > H; napply refl_eq
 ##| ##2: #H; nrewrite > (neq_to_neqbit n1 n2 H);
          napply (symmetric_eq ? (eq_bit n2 n1) false);
          napply (neq_to_neqbit n2 n1 (symmetric_neq ? n1 n2 H))
 ##]
nqed.

nlemma bitrigesim_is_comparable : comparable.
 @ bitrigesim
  ##[ napply t00
  ##| napply forall_bit
  ##| napply eq_bit
  ##| napply eqbit_to_eq
  ##| napply eq_to_eqbit
  ##| napply neqbit_to_neq
  ##| napply neq_to_neqbit
  ##| napply decidable_bit
  ##| napply symmetric_eqbit
  ##]
nqed.

unification hint 0 ≔ ⊢ carr bitrigesim_is_comparable ≡ bitrigesim.
