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

include "basic_2/reducibility/tpr_tpss.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON LOCAL ENVIRONMENTS ********************)

(* Properties concerning parallel unfold on local environments **************)

lemma ltpr_ltps_conf: ∀L1,K1,d,e. L1 [d, e] ▶ K1 → ∀L2. L1 ➡ L2 →
                      ∃∃K2. L2 [d, e] ▶* K2 & K1 ➡ K2.
#L1 #K1 #d #e #H elim H -L1 -K1 -d -e
[ /2 width=3/
| #L1 #I #V1 #X #H
  elim (ltpr_inv_pair1 … H) -H #L2 #V2 #HL12 #HV12 #H destruct /3 width=5/
| #L1 #K1 #I #V1 #W1 #e #_ #HVW1 #IHLK1 #X #H
  elim (ltpr_inv_pair1 … H) -H #L2 #V2 #HL12 #HV12 #H destruct
  elim (IHLK1 … HL12) -L1 #K2 #HLK2 #HK12
  elim (tpr_tps_ltpr … HV12 … HVW1 … HK12) -V1 /3 width=5/
| #L1 #K1 #I #V1 #W1 #d #e #_ #HVW1 #IHLK1 #X #H
  elim (ltpr_inv_pair1 … H) -H #L2 #V2 #HL12 #HV12 #H destruct
  elim (IHLK1 … HL12) -L1 #K2 #HLK2 #HK12
  elim (tpr_tps_ltpr … HV12 … HVW1 … HK12) -V1 /3 width=5/
]
qed.

lemma ltpr_ltpss_conf: ∀L1,K1,d,e. L1 [d, e] ▶* K1 → ∀L2. L1 ➡ L2 →
                       ∃∃K2. L2 [d, e] ▶* K2 & K1 ➡ K2.
#L1 #K1 #d #e #H @(ltpss_ind … H) -K1 /2 width=3/
#K #K1 #_ #HK1 #IHK #L2 #HL12
elim (IHK … HL12) -L1 #K2 #HLK2 #HK2
elim (ltpr_ltps_conf … HK1 … HK2) -K #K #HK2 #HK1
lapply (ltpss_trans_eq … HLK2 HK2) -K2 /2 width=3/
qed.
