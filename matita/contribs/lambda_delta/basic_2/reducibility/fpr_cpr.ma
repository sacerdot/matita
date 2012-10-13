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

include "basic_2/reducibility/cfpr_cpr.ma".

(* FOCALIZED PARALLEL REDUCTION ON CLOSURES *********************************)

(* Advanced propertis *******************************************************)

lemma fpr_bind_sn: ∀L1,L2,V1,V2. ⦃L1, V1⦄ ➡ ⦃L2, V2⦄ → ∀T1,T2. T1 ➡ T2 →
                   ∀a,I. ⦃L1, ⓑ{a,I}V1.T1⦄ ➡ ⦃L2, ⓑ{a,I}V2.T2⦄.
#L1 #L2 #V1 #V2 #H #T1 #T2 #HT12 #a #I
elim (fpr_inv_all … H) /3 width=4/
qed.

(* Advanced forward lemmas **************************************************)

lemma fpr_fwd_shift_bind_minus: ∀I1,I2,L1,L2,V1,V2,T1,T2.
                                ⦃L1, -ⓑ{I1}V1.T1⦄ ➡ ⦃L2, -ⓑ{I2}V2.T2⦄ →
                                ⦃L1, V1⦄ ➡ ⦃L2, V2⦄ ∧ I1 = I2.
* #I2 #L1 #L2 #V1 #V2 #T1 #T2 #H
elim (fpr_inv_all … H) -H #L #HL1 #H #HL2
[ elim (cpr_inv_abbr1 … H) -H *
  [ #V #V0 #T #HV1 #HV0 #_ #H destruct /4 width=4/
  | #T #_ #_ #H destruct
  ]
| elim (cpr_inv_abst1 … H Abst V2) -H
  #V #T #HV1 #_ #H destruct /3 width=4/
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma fpr_inv_pair1: ∀I,K1,L2,V1,T1,T2. ⦃K1.ⓑ{I}V1, T1⦄ ➡ ⦃L2, T2⦄ →
                     ∃∃K2,V2. ⦃K1, V1⦄  ➡ ⦃K2, V2⦄ &
                              ⦃K1, -ⓑ{I}V1.T1⦄ ➡ ⦃K2, -ⓑ{I}V2.T2⦄  &
                              L2 = K2.ⓑ{I}V2.
#I1 #K1 #X #V1 #T1 #T2 #H
elim (fpr_fwd_pair1 … H) -H #I2 #K2 #V2 #HT12 #H destruct
elim (fpr_fwd_shift_bind_minus … HT12) #HV12 #H destruct /2 width=5/
qed-.

lemma fpr_inv_pair3: ∀I,L1,K2,V2,T1,T2. ⦃L1, T1⦄ ➡ ⦃K2.ⓑ{I}V2, T2⦄ →
                     ∃∃K1,V1. ⦃K1, V1⦄  ➡ ⦃K2, V2⦄ &
                              ⦃K1, -ⓑ{I}V1.T1⦄ ➡ ⦃K2, -ⓑ{I}V2.T2⦄  &
                              L1 = K1.ⓑ{I}V1.
#I2 #X #K2 #V2 #T1 #T2 #H
elim (fpr_fwd_pair3 … H) -H #I1 #K1 #V1 #HT12 #H destruct
elim (fpr_fwd_shift_bind_minus … HT12) #HV12 #H destruct /2 width=5/
qed-.
