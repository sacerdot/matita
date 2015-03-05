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

(* This file was automatically generated: do not edit *********************)

include "basic_1/C/defs.ma".

definition ex1_c:
 C
\def
 let TMP_1 \def (CSort O) in (let TMP_2 \def (Bind Abst) in (let TMP_3 \def 
(TSort O) in (let TMP_4 \def (CHead TMP_1 TMP_2 TMP_3) in (let TMP_5 \def 
(Bind Abst) in (let TMP_6 \def (TSort O) in (let TMP_7 \def (CHead TMP_4 
TMP_5 TMP_6) in (let TMP_8 \def (Bind Abst) in (let TMP_9 \def (TLRef O) in 
(CHead TMP_7 TMP_8 TMP_9))))))))).

definition ex1_t:
 T
\def
 let TMP_1 \def (Flat Appl) in (let TMP_2 \def (TLRef O) in (let TMP_3 \def 
(Bind Abst) in (let TMP_4 \def (S O) in (let TMP_5 \def (S TMP_4) in (let 
TMP_6 \def (TLRef TMP_5) in (let TMP_7 \def (TSort O) in (let TMP_8 \def 
(THead TMP_3 TMP_6 TMP_7) in (THead TMP_1 TMP_2 TMP_8)))))))).

