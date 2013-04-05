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

(* CONTEXT-FREE PARALLEL REDUCTION ON LOCAL ENVIRONMENTS ********************)

(* Properties concerning parallel substitution on terms *********************)

(* Basic_1: was: pr0_subst1_fwd *)
lemma ltpr_tps_conf: ∀L1,T1,T2,d,e. L1 ⊢ T1 ▶ [d, e] T2 → ∀L2. L1 ➡ L2 →
                     ∃∃T. L2 ⊢ T1 ▶ [d, e] T & T2 ➡ T.
#L1 #T1 #T2 #d #e #H elim H -L1 -T1 -T2 -d -e
[ /2 width=3/
| #L1 #K1 #V1 #W1 #i #d #e #Hdi #Hide #HLK1 #HVW1 #L2 #HL12
  elim (ltpr_ldrop_conf … HLK1 … HL12) -L1 #X #H #HLK2
  elim (ltpr_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct -K1
  elim (lift_total V2 0 (i+1)) #W2 #HVW2
  lapply (tpr_lift … HV12 … HVW1 … HVW2) -V1 /3 width=4/
| #L1 #a #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #L2 #HL12
  elim (IHV12 … HL12) -IHV12 #V #HV1 #HV2
  elim (IHT12 (L2.ⓑ{I}V) ?) /2 width=1/ -L1 /3 width=5/
| #L1 #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #L2 #HL12
  elim (IHV12 … HL12) -IHV12
  elim (IHT12 … HL12) -L1 /3 width=5/
]
qed-.

(* Basic_1: was: pr0_subst1_back *)
lemma ltpr_tps_trans: ∀L2,T1,T2,d,e. L2 ⊢ T1 ▶ [d, e] T2 → ∀L1. L1 ➡ L2 →
                      ∃∃T. L1 ⊢ T1 ▶ [d, e] T & T ➡ T2.
#L2 #T1 #T2 #d #e #H elim H -L2 -T1 -T2 -d -e
[ /2 width=3/
| #L2 #K2 #V2 #W2 #i #d #e #Hdi #Hide #HLK2 #HVW2 #L1 #HL12
  elim (ltpr_ldrop_trans_O1 … HL12 … HLK2) -L2 #X #HLK1 #H
  elim (ltpr_inv_pair2 … H) -H #K1 #V1 #HK12 #HV12 #H destruct -K2
  elim (lift_total V1 0 (i+1)) #W1 #HVW1
  lapply (tpr_lift … HV12 … HVW1 … HVW2) -V2 /3 width=4/
| #L2 #a #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #L1 #HL12
  elim (IHV12 … HL12) -IHV12 #V #HV1 #HV2
  elim (IHT12 (L1.ⓑ{I}V) ?) /2 width=1/ -L2 /3 width=5/
| #L2 #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #L1 #HL12
  elim (IHV12 … HL12) -IHV12
  elim (IHT12 … HL12) -L2 /3 width=5/
]
qed-.
