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

include "Basic-1/T/defs.ma".

inductive C: Set \def
| CSort: nat \to C
| CHead: C \to (K \to (T \to C)).

definition cweight:
 C \to nat
\def
 let rec cweight (c: C) on c: nat \def (match c with [(CSort _) \Rightarrow O 
| (CHead c0 _ t) \Rightarrow (plus (cweight c0) (tweight t))]) in cweight.

definition clt:
 C \to (C \to Prop)
\def
 \lambda (c1: C).(\lambda (c2: C).(lt (cweight c1) (cweight c2))).

definition cle:
 C \to (C \to Prop)
\def
 \lambda (c1: C).(\lambda (c2: C).(le (cweight c1) (cweight c2))).

definition CTail:
 K \to (T \to (C \to C))
\def
 let rec CTail (k: K) (t: T) (c: C) on c: C \def (match c with [(CSort n) 
\Rightarrow (CHead (CSort n) k t) | (CHead d h u) \Rightarrow (CHead (CTail k 
t d) h u)]) in CTail.

