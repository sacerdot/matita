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

include "ground/arith/int_opp_pred_succ.ma".
include "ground/arith/int_plus.ma".

(* ADDITION FOR INTEGERS ****************************************************)

interpretation
  "subtraction (integers)"
  'minus z1 z2 = (zplus z1 (zopp z2)).

(* Constructions with zopp **************************************************)

lemma zplus_opp_self (z):
      (𝟎) = -z + z.
@int_ind_steps // #z #IH
<zopp_succ <zplus_pred_sn <zplus_succ_dx //
qed.

lemma zplus_self_opp (z):
      (𝟎) = z - z.
#z <zplus_comm //
qed.

lemma zplus_minus_simpl (z1) (z2):
      z1 = z1 + z2 - z2.
// qed.

lemma zminus_plus_simpl (z1) (z2):
      z1 = z1 - z2 + z2.
// qed.

(* Inversions with zopp *****************************************************)

lemma eq_inv_zplus_sn_sn (z) (z1) (z2):
      z + z1 = z2 → z1 = -z + z2.
#z #z1 #z2 #Hz <Hz -Hz //
qed-.

lemma eq_inv_zplus_dx_sn (z) (z1) (z2):
      z1 + z = z2 → z1 = z2 - z.
#z #z1 #z2 #Hz <Hz -Hz //
qed-.

lemma eq_inv_zplus_sn_dx (z) (z1) (z2):
      z1 = z + z2 → -z + z1 = z2.
#z #z1 #z2 #Hz >Hz -Hz //
qed-.

lemma eq_inv_zplus_dx_dx (z) (z1) (z2):
      z1 = z2 + z → z1 - z = z2.
#z #z1 #z2 #Hz >Hz -Hz //
qed-.

lemma eq_inv_zplus_sn_bi (z) (z1) (z2):
      z + z1 = z + z2 → z1 = z2.
#z #z1 #z2 #Hz
<(eq_inv_zplus_sn_dx … Hz) -Hz //
qed-.

lemma eq_inv_zplus_dx_bi (z) (z1) (z2):
      z1 + z = z2 + z → z1 = z2.
#z #z1 #z2 #Hz
<(eq_inv_zplus_dx_dx … Hz) -Hz //
qed-.

lemma eq_inv_zero_zplus (z1) (z2):
      (𝟎) = z1 + z2 → -z1 = z2.
#z1 #z2 #Hz
<(eq_inv_zplus_sn_dx … Hz) -Hz //
qed-.

lemma eq_inv_zplus_zero (z1) (z2):
      z1 + z2 = 𝟎 → -z1 = z2.
#z1 #z2 #Hz
>(eq_inv_zplus_sn_sn … Hz) -Hz //
qed-.

(* Main constructions with zopp *********************************************)

lemma zplus_opp_bi (z1) (z2):
      -(z2 + z1) = -z1 - z2.
#z1 #z2
@eq_inv_zero_zplus
<zplus_assoc //
qed.
