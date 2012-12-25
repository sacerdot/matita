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

include "basic_2/reducibility/ltpr_ldrop.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON TERMS *********************************)

(* Properties on parallel substitution for terms ****************************)

(* Basic_1: was: pr0_subst1_fwd *)
lemma ltpr_tpr_conf: ∀L1,T,U1,d,e. L1 ⊢ T ▶ [d, e] U1 → ∀L2. L1 ➡ L2 →
                     ∃∃U2. U1 ➡ U2 & L2 ⊢ T ▶ [d, e] U2.
#L1 #T #U1 #d #e #H elim H -L1 -T -U1 -d -e
[ /2 width=3/
| #L1 #K1 #V1 #W1 #i #d #e #Hdi #Hide #HLK1 #HVW1 #L2 #HL12
  elim (ltpr_ldrop_conf … HLK1 … HL12) -L1 #X #H #HLK2
  elim (ltpr_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct -K1
  elim (lift_total V2 0 (i+1)) #W2 #HVW2
  lapply (tpr_lift … HV12 … HVW1 … HVW2) -V1 /3 width=6/
| #L1 #a #I #V #W1 #T #U1 #d #e #_ #_ #IHV #IHT #L2 #HL12
  elim (IHV … HL12) -IHV #W2 #HW12
  elim (IHT (L2.ⓑ{I}W2) ?) -IHT /2 width=1/ -L1 /3 width=5/
| #L1 #I #V #W1 #T #U1 #d #e #_ #_ #IHV #IHT #L2 #HL12
  elim (IHV … HL12) -IHV
  elim (IHT … HL12) -IHT -HL12 /3 width=5/
]
qed.

(* Basic_1: was: pr0_subst1_back *)
lemma ltpr_tps_trans: ∀L2,T,U2,d,e. L2 ⊢ T ▶ [d, e] U2 → ∀L1. L1 ➡ L2 →
                      ∃∃U1. U1 ➡ U2 & L1 ⊢ T ▶ [d, e] U1.
#L2 #T #U2 #d #e #H elim H -L2 -T -U2 -d -e
[ /2 width=3/
| #L2 #K2 #V2 #W2 #i #d #e #Hdi #Hide #HLK2 #HVW2 #L1 #HL12
  elim (ltpr_ldrop_trans_O1 … HL12 … HLK2) -L2 #X #HLK1 #H
  elim (ltpr_inv_pair2 … H) -H #K1 #V1 #HK12 #HV12 #H destruct -K2
  elim (lift_total V1 0 (i+1)) #W1 #HVW1
  lapply (tpr_lift … HV12 … HVW1 … HVW2) -V2 /3 width=6/
| #L2 #a #I #V #W2 #T #U2 #d #e #_ #_ #IHV #IHT #L1 #HL12
  elim (IHV … HL12) -IHV #W1 #HW12
  elim (IHT (L1.ⓑ{I}W1) ?) -IHT /2 width=1/ -L2 /3 width=5/
| #L2 #I #V #W2 #T #U2 #d #e #_ #_ #IHV #IHT #L1 #HL12
  elim (IHV … HL12) -IHV
  elim (IHT … HL12) -IHT -HL12 /3 width=5/
]
qed.
