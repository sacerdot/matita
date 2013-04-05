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

include "basic_2/unfold/cpss_lift.ma".
include "basic_2/unfold/lcpss.ma".

(* SN PARALLEL UNFOLD FOR LOCAL ENVIRONMENTS ********************************)

(* Properies on local environment slicing ***********************************)

lemma lcpss_ldrop_conf: dropable_sn lcpss.
#L1 #K1 #d #e #H elim H -L1 -K1 -d -e
[ #d #e #X #H
  lapply (lcpss_inv_atom1 … H) -H #H destruct /2 width=3/
| #L1 #I #V1 #X #H
  elim (lcpss_inv_pair1 … H) -H #L2 #V2 #HL12 #HV12 #H destruct /3 width=3/
| #L1 #K1 #I #V1 #e #_ #IHLK1 #X #H
  elim (lcpss_inv_pair1 … H) -H #L2 #V2 #HL12 #HV12 #H destruct
  elim (IHLK1 … HL12) -IHLK1 -HL12 /3 width=3/
| #L1 #K1 #I #V1 #W1 #d #e #HLK1 #HWV1 #IHLK1 #X #H
  elim (lcpss_inv_pair1 … H) -H #L2 #V2 #HL12 #HV12 #H destruct
  elim (cpss_inv_lift1 … HV12 … HLK1 … HWV1) -HLK1 -V1
  elim (IHLK1 … HL12) -IHLK1 -HL12 /3 width=5/
]
qed-.

lemma ldrop_lcpss_trans: dedropable_sn lcpss.
#L1 #K1 #d #e #H elim H -L1 -K1 -d -e
[ #d #e #X #H
  lapply (lcpss_inv_atom1 … H) -H #H destruct /2 width=3/
| #L1 #I #V1 #X #H
  elim (lcpss_inv_pair1 … H) -H #L2 #V2 #HL12 #HV12 #H destruct /3 width=3/
| #L1 #K1 #I #V1 #e #_ #IHLK1 #K2 #HK12
  elim (IHLK1 … HK12) -IHLK1 -HK12 /3 width=5/
| #L1 #K1 #I #V1 #W1 #d #e #HLK1 #HWV1 #IHLK1 #X #H
  elim (lcpss_inv_pair1 … H) -H #L2 #W2 #HL12 #HW12 #H destruct
  elim (lift_total W2 d e) #V2 #HWV2
  lapply (cpss_lift … HW12 … HLK1 … HWV1 … HWV2) -W1 -HLK1
  elim (IHLK1 … HL12) -IHLK1 -HL12 /3 width=5/
]
qed-.

fact lcpss_ldrop_trans_O1_aux: ∀L2,K2,d,e. ⇩[d, e] L2 ≡ K2 → ∀L1. L1 ⊢ ▶* L2 →
                               d = 0 → ∃∃K1. ⇩[0, e] L1 ≡ K1 & K1 ⊢ ▶* K2.
#L2 #K2 #d #e #H elim H -L2 -K2 -d -e
[ #d #e #X #H >(lcpss_inv_atom2 … H) -H /2 width=3/
| #K2 #I #V2 #X #H
  elim (lcpss_inv_pair2 … H) -H #K1 #V1 #HK12 #HV12 #H destruct /3 width=5/
| #L2 #K2 #I #V2 #e #_ #IHLK2 #X #H #_
  elim (lcpss_inv_pair2 … H) -H #L1 #V1 #HL12 #HV12 #H destruct
  elim (IHLK2 … HL12 ?) -L2 // /3 width=3/
| #L2 #K2 #I #V2 #W2 #d #e #_ #_ #_ #L1 #_
  >commutative_plus normalize #H destruct
]
qed-.

lemma lcpss_ldrop_trans_O1: dropable_dx lcpss.
/2 width=5 by lcpss_ldrop_trans_O1_aux/ qed-.
