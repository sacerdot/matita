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

include "pointer_sequence.ma".

(* POINTER TREE *************************************************************)

(* Policy: pointer tree metavariables: P, Q *)
(* Note: this is a binary tree on pointer sequences *)
inductive ptree: Type[0] ≝
| tnil : ptree
| tcons: pseq → ptree → ptree → ptree
.

let rec size (P:ptree) on P ≝ match P with
[ tnil          ⇒ 0
| tcons s Q1 Q2 ⇒ size Q2 + size Q1 + |s|
].

interpretation "pointer tree size" 'card P = (size P).
