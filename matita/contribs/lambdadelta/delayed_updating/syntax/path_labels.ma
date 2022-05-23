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

include "delayed_updating/syntax/path.ma".
include "delayed_updating/notation/functions/power_2.ma".
include "ground/arith/nat_succ_iter.ma".

(* *)

definition labels (l) (n:nat): path ≝
           ((list_lcons ? l)^n) (𝐞).

interpretation
  "labels (path)"
  'Power l n = (labels l n).

(* Basic constructions ******************************************************)

lemma labels_unfold (l) (n):
      ((list_lcons ? l)^n) (𝐞) = l∗∗n.
// qed.

lemma labels_zero (l):
      (𝐞) = l∗∗𝟎.
// qed.

lemma labels_succ (l) (n):
      l◗(l∗∗n) = l∗∗(↑n).
#l #n
<labels_unfold <labels_unfold <niter_succ //
qed.

(* Basic inversions *********************************************************)

lemma eq_inv_empty_labels (l) (n):
      (𝐞) = l∗∗n → 𝟎 = n.
#l #n @(nat_ind_succ … n) -n //
#n #_ <labels_succ #H0 destruct
qed-.
