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

include "Basic_2/reducibility/tpr_lift.ma".
include "Basic_2/reducibility/ltpr.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON LOCAL ENVIRONMENTS ********************)

(* Basic_1: was: wcpr0_ldrop *)
lemma ltpr_ldrop_conf: ∀L1,K1,d,e. ⇩[d, e] L1 ≡ K1 → ∀L2. L1 ➡ L2 →
                       ∃∃K2. ⇩[d, e] L2 ≡ K2 & K1 ➡ K2.
#L1 #K1 #d #e #H elim H -L1 -K1 -d -e
[ #d #e #X #H >(ltpr_inv_atom1 … H) -H /2 width=3/
| #K1 #I #V1 #X #H
  elim (ltpr_inv_pair1 … H) -H #L2 #V2 #HL12 #HV12 #H destruct /3 width=5/
| #L1 #K1 #I #V1 #e #_ #IHLK1 #X #H
  elim (ltpr_inv_pair1 … H) -H #L2 #V2 #HL12 #HV12 #H destruct
  elim (IHLK1 … HL12) -L1 /3 width=3/
| #L1 #K1 #I #V1 #W1 #d #e #_ #HWV1 #IHLK1 #X #H
  elim (ltpr_inv_pair1 … H) -H #L2 #V2 #HL12 #HV12 #H destruct
  elim (tpr_inv_lift … HV12 … HWV1) -V1
  elim (IHLK1 … HL12) -L1 /3 width=5/
]
qed.

(* Basic_1: was: wcpr0_ldrop_back *)
lemma ldrop_ltpr_trans: ∀L1,K1,d,e. ⇩[d, e] L1 ≡ K1 → ∀K2. K1 ➡ K2 →
                        ∃∃L2. ⇩[d, e] L2 ≡ K2 & L1 ➡ L2.
#L1 #K1 #d #e #H elim H -L1 -K1 -d -e
[ #d #e #X #H >(ltpr_inv_atom1 … H) -H /2 width=3/
| #K1 #I #V1 #X #H
  elim (ltpr_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct /3 width=5/
| #L1 #K1 #I #V1 #e #_ #IHLK1 #K2 #HK12
  elim (IHLK1 … HK12) -K1 /3 width=5/
| #L1 #K1 #I #V1 #W1 #d #e #_ #HWV1 #IHLK1 #X #H
  elim (ltpr_inv_pair1 … H) -H #K2 #W2 #HK12 #HW12 #H destruct
  elim (lift_total W2 d e) #V2 #HWV2
  lapply (tpr_lift … HW12 … HWV1 … HWV2) -W1
  elim (IHLK1 … HK12) -K1 /3 width=5/
]
qed.

fact ltpr_ldrop_trans_O1_aux: ∀L2,K2,d,e. ⇩[d, e] L2 ≡ K2 → ∀L1. L1 ➡ L2 →
                              d = 0 → ∃∃K1. ⇩[0, e] L1 ≡ K1 & K1 ➡ K2.
#L2 #K2 #d #e #H elim H -L2 -K2 -d -e
[ #d #e #X #H >(ltpr_inv_atom2 … H) -H /2 width=3/
| #K2 #I #V2 #X #H
  elim (ltpr_inv_pair2 … H) -H #K1 #V1 #HK12 #HV12 #H destruct /3 width=5/
| #L2 #K2 #I #V2 #e #_ #IHLK2 #X #H #_
  elim (ltpr_inv_pair2 … H) -H #L1 #V1 #HL12 #HV12 #H destruct
  elim (IHLK2 … HL12 ?) -L2 // /3 width=3/
| #L2 #K2 #I #V2 #W2 #d #e #_ #_ #_ #L1 #_
  >commutative_plus normalize #H destruct
]
qed.

lemma ltpr_ldrop_trans_O1: ∀L1,L2. L1 ➡ L2 → ∀K2,e. ⇩[0, e] L2 ≡ K2 →
                           ∃∃K1. ⇩[0, e] L1 ≡ K1 & K1 ➡ K2.
/2 width=5/ qed.
