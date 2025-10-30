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

include "ground/relocation/fb/fbr_bext.ma".
include "ground/lib/bool_minus.ma".

(* SUBTRACTION FOR FINITE RELOCATION MAPS WITH BOOLEANS *********************)

interpretation
  "subtraction (finite relocation maps with booleans)"
  'minus f1 f2 = (fbr_bext bminus f1 f2).

(* Basic constructions ******************************************************)

lemma fbr_minus_id_sx (f2):
      (𝐢) = 𝐢-f2.
// qed.

lemma fbr_minus_id_dx (f1):
      f1 = f1-𝐢.
/2 width=1 by fbr_bext_id_dx_true/
qed.

lemma fbr_minus_push_rcons (f1) (f2) (b2):
      (⫯(f1-f2)) = (⫯f1)-(f2◖b2).
// qed.

lemma fbr_minus_next_push (f1) (f2):
      ↑(f1-f2) = (↑f1)-(⫯f2).
// qed.

lemma fbr_minus_next_bi (f1) (f2):
      (⫯(f1-f2)) = (↑f1)-(↑f2).
// qed.

(* Advanced constructions ***************************************************)

lemma fbr_minus_rcons_push (f1) (f2) (b1):
      (f1-f2)◖b1 = (f1◖b1)-(⫯f2).
#f1 #f2 * //
qed.
