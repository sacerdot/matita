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
include "basic_2/equivalence/lsubse_ldrop.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR CONTEXT-SENSITIVE PARALLEL EQUIVALENCE **)

(* Properties on stratified native type assignment **************************)

lemma lsubse_ssta_trans: ∀h,g,L2,T,U2,l. ⦃h, L2⦄ ⊢ T •[g,l] U2 →
                         ∀L1. h ⊢ L1 ⊢•⊑[g] L2 →
                         ∃∃U1. ⦃h, L1⦄ ⊢ T •[g,l] U1 & L1 ⊢ U1 ⬌* U2.
#h #g #L2 #T #U #l #H elim H -L2 -T -U -l
[ /3 width=3/
| #L2 #K2 #V2 #W2 #U2 #i #l #HLK2 #_ #HWU2 #IHVW2 #L1 #HL12
  elim (lsubse_ldrop_O1_trans … HL12 … HLK2) -L2 #X #H #HLK1
  elim (lsubse_inv_pair2 … H) -H * #K1 [ | -HWU2 -IHVW2 -HLK1 ]
  [ #HK12 #H destruct
    elim (IHVW2 … HK12) -K2 #T2 #HVT2 #HTW2
    lapply (ldrop_fwd_ldrop2 … HLK1) #H
    elim (lift_total T2 0 (i+1)) /3 width=11/
  | #W1 #V1 #W2 #l0 #_ #_ #_ #_ #_ #H destruct
  ]
| #L2 #K2 #W2 #V2 #U2 #i #l #HLK2 #HWV2 #HWU2 #IHWV2 #L1 #HL12
  elim (lsubse_ldrop_O1_trans … HL12 … HLK2) -L2 #X #H #HLK1
  elim (lsubse_inv_pair2 … H) -H * #K1 [ -HWV2 | -IHWV2 ]
  [ #HK12 #H destruct
    elim (IHWV2 … HK12) -K2 /3 width=6/
  | #W1 #V1 #T2 #l0 #HVW1 #HWT2 #HW12 #_ #H #_ destruct
    elim (ssta_mono … HWV2 … HWT2) -HWV2 -HWT2 #H1 #H2 destruct
    lapply (ldrop_fwd_ldrop2 … HLK1) #H
    elim (lift_total W1 0 (i+1)) /3 width=11/
  ]
| #a #I #L2 #V2 #T2 #U2 #l #_ #IHTU2 #L1 #HL12
  elim (IHTU2 (L1.ⓑ{I}V2) …) [2: /2 width=1/ ] -L2 /3 width=3/
| #L2 #V2 #T2 #U2 #l #_ #IHTU2 #L1 #HL12
  elim (IHTU2 … HL12) -L2 /3 width=5/
| #L2 #W2 #T2 #U2 #l #_ #IHTU2 #L1 #HL12
  elim (IHTU2 … HL12) -L2 /3 width=3/
]
qed.
