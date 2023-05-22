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

include "ground/arith/int_pred_succ.ma".
include "ground/arith/pnat_iter.ma".

(* ADDITION FOR INTEGERS ****************************************************)

definition zplus (z1) (z2): ℤ ≝
           zsplit … (λp.(zpred^p)z1) (z1) (λp.(zsucc^p)z1) z2
.

interpretation
  "addition (integers)"
  'plus z1 z2 = (zplus z1 z2).

(* Basic constructions ******************************************************)

lemma zplus_neg_succ_dx (z) (p):
      ↓(z + −p) = z + −↑p.
// qed.

lemma zplus_neg_unit_dx (z):
      ↓z = z + −𝟏.
// qed.

lemma zplus_zero_dx (z):
      z = z + 𝟎.
// qed.

lemma zplus_pos_unit_dx (z):
      ↑z = z + ⁤𝟏.
// qed.

lemma zplus_pos_succ_dx (z) (p):
      ↑(z + ⁤p) = z + ⁤↑p.
// qed.

(* Advanced constructions ***************************************************)

lemma zplus_succ_dx (z1) (z2):
      ↑(z1 + z2) = z1 + ↑z2.
#z1 @int_ind_psucc // #p2 #_
<zplus_neg_succ_dx <zsucc_pred //
qed.

lemma zplus_pred_dx (z1) (z2):
      ↓(z1 + z2) = z1 + ↓z2.
#z1 @int_ind_psucc // #p2 #_
<zplus_pos_succ_dx <zpred_succ //
qed.

lemma zplus_zero_sn (z):
      z = 𝟎 +z.
#z @(int_ind_psucc … z) -z //
#z #H0 

qed.

lemma zplus_succ_sn (z1) (z2):
      ↑(z1 + z2) = ↑z1 + z2.
#z1 @int_ind_psucc // #p2 #IH
<zplus_neg_succ_dx <zplus_neg_succ_dx
<IH -IH <zpred_succ <zsucc_pred //
qed.

lemma zplus_pred_sn (z1) (z2):
      ↓(z1 + z2) = ↓z1 + z2.
#z1 @int_ind_psucc // #p2 #IH
<zplus_pos_succ_dx <zplus_pos_succ_dx
<IH -IH <zpred_succ <zsucc_pred //
qed.

(* Main constructions *******************************************************)

lemma zplus_comm: commutative … zplus.
@int_ind_steps //
qed-.

lemma zplus_assoc: associative … zplus.
#z1 #z2
@int_ind_steps // #z3 #IH
[ <zplus_pred_dx <zplus_pred_dx <zplus_pred_dx //
| <zplus_succ_dx <zplus_succ_dx <zplus_succ_dx //
]
qed.
