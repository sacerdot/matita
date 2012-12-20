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

include "pointer_list.ma".

(* POINTER TREE *************************************************************)

(* Policy: pointer tree metavariables: P, Q *)
(* Note: this is a binary tree on pointer sequences *)
inductive ptrt: Type[0] ≝
| tnil : ptrt
| tcons: ptrl → ptrt → ptrt → ptrt
.

let rec length (P:ptrt) on P ≝ match P with
[ tnil          ⇒ 0
| tcons s Q1 Q2 ⇒ length Q2 + length Q1 + |s|
].

interpretation "pointer tree length" 'card P = (length P).
