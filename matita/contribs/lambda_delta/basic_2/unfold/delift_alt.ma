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

include "basic_2/unfold/delift_lift.ma".

(* INVERSE TERM RELOCATION  *************************************************)

(* alternative definition of inverse relocation *)
inductive delifta: nat → nat → lenv → relation term ≝
| delifta_sort   : ∀L,d,e,k. delifta d e L (⋆k) (⋆k)
| delifta_lref_lt: ∀L,d,e,i. i < d → delifta d e L (#i) (#i)
| delifta_lref_be: ∀L,K,V1,V2,W2,i,d,e. d ≤ i → i < d + e →
                   ⇩[0, i] L ≡ K. ⓓV1 → delifta 0 (d + e - i - 1) K V1 V2 →
                   ⇧[0, d] V2 ≡ W2 → delifta d e L (#i) W2
| delifta_lref_ge: ∀L,d,e,i. d + e ≤ i → delifta d e L (#i) (#(i - e))
| delifta_gref   : ∀L,d,e,p. delifta d e L (§p) (§p)
| delifta_bind   : ∀L,I,V1,V2,T1,T2,d,e.
                   delifta d e L V1 V2 → delifta (d + 1) e (L. ⓑ{I} V2) T1 T2 →
                   delifta d e L (ⓑ{I} V1. T1) (ⓑ{I} V2. T2)
| delifta_flat   : ∀L,I,V1,V2,T1,T2,d,e.
                   delifta d e L V1 V2 → delifta d e L T1 T2 →
                   delifta d e L (ⓕ{I} V1. T1) (ⓕ{I} V2. T2)
.

interpretation "inverse relocation (term) alternative"
   'TSubstAlt L T1 d e T2 = (delifta d e L T1 T2).

(* Basic properties *********************************************************)

lemma delifta_lsubs_conf: ∀L1,T1,T2,d,e. L1 ⊢ T1 [d, e] ≡≡ T2 →
                          ∀L2. L1 [d, e] ≼ L2 → L2 ⊢ T1 [d, e] ≡≡ T2.
#L1 #T1 #T2 #d #e #H elim H -L1 -T1 -T2 -d -e // /2 width=1/
[ #L1 #K1 #V1 #V2 #W2 #i #d #e #Hdi #Hide #HLK1 #_ #HVW2 #IHV12 #L2 #HL12
  elim (ldrop_lsubs_ldrop1_abbr … HL12 … HLK1 ? ?) -HL12 -HLK1 // /3 width=6/
| /4 width=1/
| /3 width=1/
]
qed.

lemma delift_delifta: ∀L,T1,T2,d,e. L ⊢ T1 [d, e] ≡ T2 → L ⊢ T1 [d, e] ≡≡ T2.
#L #T1 @(cw_wf_ind … L T1) -L -T1 #L #T1 elim T1 -T1
[ * #i #IH #T2 #d #e #H
  [ >(delift_inv_sort1 … H) -H //
  | elim (delift_inv_lref1 … H) -H * /2 width=1/
    #K #V1 #V2 #Hdi #Hide #HLK #HV12 #HVT2
    lapply (ldrop_pair2_fwd_cw … HLK) #H
    lapply (IH … HV12) // -H /2 width=6/
  | >(delift_inv_gref1 … H) -H //
  ]
| * #I #V1 #T1 #_ #_ #IH #X #d #e #H
  [ elim (delift_inv_bind1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
    lapply (delift_lsubs_conf … HT12 (L.ⓑ{I}V1) ?) -HT12 /2 width=1/ #HT12
    lapply (IH … HV12) -HV12 // #HV12
    lapply (IH … HT12) -IH -HT12 /2 width=1/ #HT12
    lapply (delifta_lsubs_conf … HT12 (L.ⓑ{I}V2) ?) -HT12 /2 width=1/
  | elim (delift_inv_flat1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
    lapply (IH … HV12) -HV12 //
    lapply (IH … HT12) -IH -HT12 // /2 width=1/
  ]
]
qed.

(* Basic inversion lemmas ***************************************************)

lemma delifta_delift: ∀L,T1,T2,d,e. L ⊢ T1 [d, e] ≡≡ T2 → L ⊢ T1 [d, e] ≡ T2.
#L #T1 #T2 #d #e #H elim H -L -T1 -T2 -d -e // /2 width=1/ /2 width=6/
qed-. 

lemma delift_ind_alt: ∀R:ℕ→ℕ→lenv→relation term.
                      (∀L,d,e,k. R d e L (⋆k) (⋆k)) →
                      (∀L,d,e,i. i < d → R d e L (#i) (#i)) →
                      (∀L,K,V1,V2,W2,i,d,e. d ≤ i → i < d + e →
                       ⇩[O, i] L ≡ K.ⓓV1 → K ⊢ V1 [O, d + e - i - 1] ≡ V2 →
                       ⇧[O, d] V2 ≡ W2 → R O (d+e-i-1) K V1 V2 → R d e L #i W2
                      ) →
                      (∀L,d,e,i. d + e ≤ i → R d e L (#i) (#(i - e))) →
                      (∀L,d,e,p. R d e L (§p) (§p)) →
                      (∀L,I,V1,V2,T1,T2,d,e. L ⊢ V1 [d, e] ≡ V2 →
                       L.ⓑ{I}V2 ⊢ T1 [d + 1, e] ≡ T2 → R d e L V1 V2 →
                       R (d+1) e (L.ⓑ{I}V2) T1 T2 → R d e L (ⓑ{I}V1.T1) (ⓑ{I}V2.T2)
                      ) →
                      (∀L,I,V1,V2,T1,T2,d,e. L ⊢ V1 [d, e] ≡ V2 →
                       L⊢ T1 [d, e] ≡ T2 → R d e L V1 V2 →
                       R d e L T1 T2 → R d e L (ⓕ{I}V1.T1) (ⓕ{I}V2.T2)
                      ) →
                      ∀d,e,L,T1,T2. L ⊢ T1 [d, e] ≡ T2 → R d e L T1 T2.
#R #H1 #H2 #H3 #H4 #H5 #H6 #H7 #d #e #L #T1 #T2 #H elim (delift_delifta … H) -L -T1 -T2 -d -e
// /2 width=1 by delifta_delift/ /3 width=1 by delifta_delift/ /3 width=7 by delifta_delift/
qed-.
