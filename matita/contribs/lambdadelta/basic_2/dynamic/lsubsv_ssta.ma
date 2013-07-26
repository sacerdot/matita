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

include "basic_2/static/ssta_ssta.ma".
include "basic_2/equivalence/cpcs_cpcs.ma".
include "basic_2/dynamic/lsubsv_ldrop.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR STRATIFIED NATIVE VALIDITY **************)

(* Properties on stratified static type assignment **************************)

lemma lsubsv_ssta_trans: ∀h,g,L2,T,U2,l. ⦃h, L2⦄ ⊢ T •[g] ⦃l, U2⦄ →
                         ∀L1. h ⊢ L1 ¡⊑[g] L2 →
                         ∃∃U1. ⦃h, L1⦄ ⊢ T •[g] ⦃l, U1⦄ & L1 ⊢ U1 ⬌* U2.
#h #g #L2 #T #U #l #H elim H -L2 -T -U -l
[ /3 width=3/
| #L2 #K2 #X #Y #U #i #l #HLK2 #_ #HYU #IHXY #L1 #HL12
  elim (lsubsv_ldrop_O1_trans … HL12 … HLK2) -L2 #X #H #HLK1
  elim (lsubsv_inv_pair2 … H) -H * #K1 [ | -HYU -IHXY -HLK1 ]
  [ #HK12 #H destruct
    elim (IHXY … HK12) -K2 #T #HXT #HTY
    lapply (ldrop_fwd_ldrop2 … HLK1) #H
    elim (lift_total T 0 (i+1)) /3 width=11/
  | #V #W1 #V2 #l0 #_ #_ #_ #_ #_ #H destruct
  ]
| #L2 #K2 #Y #X #U #i #l #HLK2 #HYX #HYU #IHYX #L1 #HL12
  elim (lsubsv_ldrop_O1_trans … HL12 … HLK2) -L2 #X #H #HLK1
  elim (lsubsv_inv_pair2 … H) -H * #K1 [ -HYX | -IHYX ]
  [ #HK12 #H destruct
    elim (IHYX … HK12) -K2 /3 width=6/
  | #V #W1 #V2 #l0 #HYV #_ #HV #HY #_ #_ #H destruct
    elim (snv_inv_cast … HYV) -HYV #W #l1 #_ #_ #HVW #HWY
    elim (ssta_mono … HVW … HV) -HV #Hl10 #_
    elim (ssta_mono … HYX … HY) -HYX -HY #H #_ destruct
    lapply (ldrop_fwd_ldrop2 … HLK1) #H
    elim (lift_total W 0 (i+1))
    /4 width=11 by cpcs_lift, ex2_intro, ssta_ldef, ssta_cast/
  ]
| #a #I #L2 #V2 #T2 #U2 #l #_ #IHTU2 #L1 #HL12
  elim (IHTU2 (L1.ⓑ{I}V2) …) [2: /2 width=1/ ] -L2 /3 width=3/
| #L2 #V2 #T2 #U2 #l #_ #IHTU2 #L1 #HL12
  elim (IHTU2 … HL12) -L2 /3 width=5/
| #L2 #W2 #T2 #U2 #l #_ #IHTU2 #L1 #HL12
  elim (IHTU2 … HL12) -L2 /3 width=3/
]
qed-.
