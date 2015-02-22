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

include "basic_1/A/defs.ma".

let rec lweight (a: A) on a: nat \def match a with [(ASort _ _) \Rightarrow O 
| (AHead a1 a2) \Rightarrow (let TMP_1 \def (lweight a1) in (let TMP_2 \def 
(lweight a2) in (let TMP_3 \def (plus TMP_1 TMP_2) in (S TMP_3))))].

definition llt:
 A \to (A \to Prop)
\def
 \lambda (a1: A).(\lambda (a2: A).(let TMP_1 \def (lweight a1) in (let TMP_2 
\def (lweight a2) in (lt TMP_1 TMP_2)))).

