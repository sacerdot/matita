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

include "basic_2/reducibility/tpr.ma".

(* FOCALIZED PARALLEL REDUCTION ON CLOSURES *********************************)

definition fpr: bi_relation lenv term ≝
                λL1,T1,L2,T2. |L1| = |L2| ∧ L1 @@ T1 ➡ L2 @@ T2.

interpretation
   "focalized parallel reduction (closure)"
   'FocalizedPRed L1 T1 L2 T2 = (fpr L1 T1 L2 T2).

(* Basic properties *********************************************************)

lemma fpr_refl: bi_reflexive … fpr.
/2 width=1/ qed.

(* Basic inversion lemmas ***************************************************)

lemma fpr_inv_atom1: ∀L2,T1,T2. ⦃⋆, T1⦄ ➡ ⦃L2, T2⦄ → T1 ➡ T2 ∧ L2 = ⋆.
#L2 #T1 #T2 * #H
lapply (length_inv_zero_sn … H) -H #H destruct /2 width=1/
qed-.

lemma fpr_inv_pair1: ∀I,K1,L2,V1,T1,T2. ⦃K1.ⓑ{I}V1, T1⦄ ➡ ⦃L2, T2⦄ →
                     ∃∃K2,V2. ⦃K1, -ⓑ{I}V1.T1⦄ ➡ ⦃K2, -ⓑ{I}V2.T2⦄  &
                              L2 = K2.ⓑ{I}V2.
#I1 #K1 #L2 #V1 #T1 #T2 * #H
elim (length_inv_pos_sn … H) -H #I2 #K2 #V2 #HK12 #H destruct #H
elim (tpr_fwd_shift_bind_minus … H) // #_ #H0 destruct /3 width=4/
qed-.

lemma fpr_inv_atom3: ∀L1,T1,T2. ⦃L1,T1⦄ ➡ ⦃⋆,T2⦄ → T1 ➡ T2 ∧ L1 = ⋆.
#L1 #T1 #T2 * #H
lapply (length_inv_zero_dx … H) -H #H destruct /2 width=1/
qed-.

lemma fpr_inv_pair3: ∀I,L1,K2,V2,T1,T2. ⦃L1, T1⦄ ➡ ⦃K2.ⓑ{I}V2, T2⦄ →
                     ∃∃K1,V1. ⦃K1, -ⓑ{I}V1.T1⦄ ➡ ⦃K2, -ⓑ{I}V2.T2⦄  &
                              L1 = K1.ⓑ{I}V1.
#I2 #L1 #K2 #V2 #T1 #T2 * #H
elim (length_inv_pos_dx … H) -H #I1 #K1 #V1 #HK12 #H destruct #H
elim (tpr_fwd_shift_bind_minus … H) // #_ #H0 destruct /3 width=4/
qed-.
