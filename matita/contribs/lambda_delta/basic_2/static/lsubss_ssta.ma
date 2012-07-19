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

include "basic_2/static/ssta_lift.ma".
include "basic_2/static/ssta_ssta.ma".
include "basic_2/static/lsubss_ldrop.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR STRATIFIED STATIC TYPE ASSIGNMENT *******)

(* Properties concerning stratified native type assignment ******************)

lemma lsubss_ssta_trans: ∀h,g,L2,T,U,l. ⦃h, L2⦄ ⊢ T •[g,l] U →
                         ∀L1. h ⊢ L1 •⊑[g] L2 → ⦃h, L1⦄ ⊢ T •[g,l] U.
#h #g #L2 #T #U #l #H elim H -L2 -T -U -l
[ /2 width=1/
| #L2 #K2 #V2 #W2 #U2 #i #l #HLK2 #_ #HWU2 #IHVW2 #L1 #HL12
  elim (lsubss_ldrop_O1_trans … HL12 … HLK2) -L2 #X #H #HLK1
  elim (lsubss_inv_pair2 … H) -H * #K1 [ | -HWU2 -IHVW2 -HLK1 ]
  [ #HK12 #H destruct /3 width=6/
  | #V1 #l0 #_ #_ #_ #_ #H destruct
  ]
| #L2 #K2 #W2 #V2 #U2 #i #l #HLK2 #HWV2 #HWU2 #IHWV2 #L1 #HL12
  elim (lsubss_ldrop_O1_trans … HL12 … HLK2) -L2 #X #H #HLK1
  elim (lsubss_inv_pair2 … H) -H * #K1 [ -HWV2 | -IHWV2 ]
  [ #HK12 #H destruct /3 width=6/
  | #V1 #l0 #H1 #H2 #_ #H #_ destruct
    elim (ssta_fwd_correct … H2) -H2 #V #H
    elim (ssta_mono … HWV2 … H) -HWV2 -H /2 width=6/
  ]
| /4 width=1/
| /3 width=1/
| /3 width=1/
]
qed.

lemma lsubss_ssta_conf: ∀h,g,L1,T,U,l. ⦃h, L1⦄ ⊢ T •[g,l] U →
                        ∀L2. h ⊢ L1 •⊑[g] L2 → ⦃h, L2⦄ ⊢ T •[g,l] U.
#h #g #L1 #T #U #l #H elim H -L1 -T -U -l
[ /2 width=1/
| #L1 #K1 #V1 #W1 #U1 #i #l #HLK1 #HVW1 #HWU1 #IHVW1 #L2 #HL12
  elim (lsubss_ldrop_O1_conf … HL12 … HLK1) -L1 #X #H #HLK2
  elim (lsubss_inv_pair1 … H) -H * #K2 [ -HVW1 | -IHVW1 ]
  [ #HK12 #H destruct /3 width=6/
  | #V2 #l0 #H1 #H2 #_ #H #_ destruct
    elim (ssta_mono … HVW1 … H1) -HVW1 -H1 #H1 #H2 destruct
    elim (ssta_fwd_correct … H2) -H2 /2 width=6/
  ]
| #L1 #K1 #W1 #V1 #U1 #i #l #HLK1 #_ #HWU1 #IHWV1 #L2 #HL12
  elim (lsubss_ldrop_O1_conf … HL12 … HLK1) -L1 #X #H #HLK2
  elim (lsubss_inv_pair1 … H) -H * #K2 [ | -HWU1 -IHWV1 -HLK2 ]
  [ #HK12 #H destruct /3 width=6/
  | #V2 #l0 #_ #_ #_ #_ #H destruct
  ]
| /4 width=1/
| /3 width=1/
| /3 width=1/
]
qed.
