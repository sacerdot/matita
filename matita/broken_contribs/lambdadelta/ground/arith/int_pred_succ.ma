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

include "ground/arith/int_pred.ma".
include "ground/arith/int_succ.ma".

(* PREDECESSOR FOR INTEGERS *************************************************)

(* Constructions with zsucc *************************************************)

lemma zpred_succ (z):
      z = ↓↑z.
* [ * [| #p ] || #p ] //
qed.

lemma zsucc_pred (z):
      z = ↑↓z.
* [ #p || * [| #p ] ] //
qed.

(* Eliminations with zsucc **************************************************)

lemma int_ind_steps (Q:predicate …):
      (∀z. Q z → Q(↓z)) →
      Q (𝟎) →
      (∀z. Q z → Q(↑z)) →
      ∀z. Q z.
#Q #IH1 #IH2 #IH3
@int_ind_psucc
/2 width=1 by/
qed-.
