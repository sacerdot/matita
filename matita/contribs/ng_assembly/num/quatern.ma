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

include "num/bool.ma".

(* ********** *)
(* QUATERNARI *)
(* ********** *)

ninductive quatern : Type ≝
  q0 : quatern
| q1 : quatern
| q2 : quatern
| q3 : quatern.

(* operatore = *)
ndefinition eq_qu ≝
λn1,n2:quatern.
 match n1 with
  [ q0 ⇒ match n2 with [ q0 ⇒ true | _ ⇒ false ]
  | q1 ⇒ match n2 with [ q1 ⇒ true | _ ⇒ false ]
  | q2 ⇒ match n2 with [ q2 ⇒ true | _ ⇒ false ]
  | q3 ⇒ match n2 with [ q3 ⇒ true | _ ⇒ false ]
  ].

(* iteratore sui quaternari *)
ndefinition forall_qu ≝ λP.
 P q0 ⊗ P q1 ⊗ P q2 ⊗ P q3.

(* operatore successorre *)
ndefinition succ_qu ≝
λn.match n with
 [ q0 ⇒ q1 | q1 ⇒ q2 | q2 ⇒ q3 | q3 ⇒ q0 ].

(* quaternari ricorsivi *)
ninductive rec_quatern : quatern → Type ≝
  qu_O : rec_quatern q0
| qu_S : ∀n.rec_quatern n → rec_quatern (succ_qu n).

(* quaternari → quaternari ricorsivi *)
ndefinition qu_to_recqu ≝
λn.match n return λx.rec_quatern x with
 [ q0 ⇒ qu_O
 | q1 ⇒ qu_S ? qu_O
 | q2 ⇒ qu_S ? (qu_S ? qu_O)
 | q3 ⇒ qu_S ? (qu_S ? (qu_S ? qu_O))
 ].
