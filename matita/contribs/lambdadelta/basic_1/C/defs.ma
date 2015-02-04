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

include "basic_1/T/defs.ma".

inductive C: Type[0] \def
| CSort: nat \to C
| CHead: C \to (K \to (T \to C)).

let rec cweight (c: C) on c: nat \def match c with [(CSort _) \Rightarrow O | 
(CHead c0 _ t) \Rightarrow (let TMP_1 \def (cweight c0) in (let TMP_2 \def 
(tweight t) in (plus TMP_1 TMP_2)))].

definition clt:
 C \to (C \to Prop)
\def
 \lambda (c1: C).(\lambda (c2: C).(let TMP_1 \def (cweight c1) in (let TMP_2 
\def (cweight c2) in (lt TMP_1 TMP_2)))).

definition cle:
 C \to (C \to Prop)
\def
 \lambda (c1: C).(\lambda (c2: C).(let TMP_1 \def (cweight c1) in (let TMP_2 
\def (cweight c2) in (le TMP_1 TMP_2)))).

let rec CTail (k: K) (t: T) (c: C) on c: C \def match c with [(CSort n) 
\Rightarrow (let TMP_2 \def (CSort n) in (CHead TMP_2 k t)) | (CHead d h u) 
\Rightarrow (let TMP_1 \def (CTail k t d) in (CHead TMP_1 h u))].

