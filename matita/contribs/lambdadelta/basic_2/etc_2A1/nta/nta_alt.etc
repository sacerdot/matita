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

include "basic_2/equivalence/cpcs_cpcs.ma".
include "basic_2/dynamic/nta.ma".

(* NATIVE TYPE ASSIGNMENT ON TERMS ******************************************)

(* alternative definition of nta *)
inductive ntaa (h:sh): lenv → relation term ≝
| ntaa_sort: ∀L,k. ntaa h L (⋆k) (⋆(next h k))
| ntaa_ldef: ∀L,K,V,W,U,i. ⇩[0, i] L ≡ K. ⓓV → ntaa h K V W →
             ⇧[0, i + 1] W ≡ U → ntaa h L (#i) U
| ntaa_ldec: ∀L,K,W,V,U,i. ⇩[0, i] L ≡ K. ⓛW → ntaa h K W V →
             ⇧[0, i + 1] W ≡ U → ntaa h L (#i) U
| ntaa_bind: ∀I,L,V,W,T,U. ntaa h L V W → ntaa h (L. ⓑ{I} V) T U →
             ntaa h L (ⓑ{I}V.T) (ⓑ{I}V.U)
| ntaa_appl: ∀L,V,W,T,U. ntaa h L V W → ntaa h L (ⓛW.T) (ⓛW.U) →
             ntaa h L (ⓐV.ⓛW.T) (ⓐV.ⓛW.U)
| ntaa_pure: ∀L,V,W,T,U. ntaa h L T U → ntaa h L (ⓐV.U) W →
             ntaa h L (ⓐV.T) (ⓐV.U)
| ntaa_cast: ∀L,T,U,W. ntaa h L T U → ntaa h L U W → ntaa h L (ⓝU. T) U
| ntaa_conv: ∀L,T,U1,U2,V2. ntaa h L T U1 → L ⊢ U1 ⬌* U2 → ntaa h L U2 V2 →
             ntaa h L T U2
.

interpretation "native type assignment (term) alternative"
   'NativeTypeAlt h L T U = (ntaa h L T U).

(* Advanced inversion lemmas ************************************************)

fact ntaa_inv_bind1_aux: ∀h,L,T,U. ⦃h, L⦄ ⊢ T :: U → ∀J,X,Y. T = ⓑ{J}Y.X →
                         ∃∃Z1,Z2. ⦃h, L⦄ ⊢ Y :: Z1 & ⦃h, L.ⓑ{J}Y⦄ ⊢ X :: Z2 &
                                  L ⊢ ⓑ{J}Y.Z2 ⬌* U.
#h #L #T #U #H elim H -L -T -U
[ #L #k #J #X #Y #H destruct
| #L #K #V #W #U #i #_ #_ #_ #_ #J #X #Y #H destruct
| #L #K #W #V #U #i #_ #_ #_ #_ #J #X #Y #H destruct
| #I #L #V #W #T #U #HVW #HTU #_ #_ #J #X #Y #H destruct /2 width=3/
| #L #V #W #T #U #_ #_ #_ #_ #J #X #Y #H destruct
| #L #V #W #T #U #_ #_ #_ #_ #J #X #Y #H destruct
| #L #T #U #W #_ #_ #_ #_ #J #X #Y #H destruct
| #L #T #U1 #U2 #V2 #_ #HU12 #_ #IHTU1 #_ #J #X #Y #H destruct
  elim (IHTU1 ????) -IHTU1 [5: // |2,3,4: skip ] #Z1 #Z2 #HZ1 #HZ2 #HU1
  lapply (cpcs_trans … HU1 … HU12) -U1 /2 width=3/
]
qed.

lemma ntaa_inv_bind1: ∀h,J,L,Y,X,U. ⦃h, L⦄ ⊢ ⓑ{J}Y.X :: U →
                      ∃∃Z1,Z2. ⦃h, L⦄ ⊢ Y :: Z1 & ⦃h, L.ⓑ{J}Y⦄ ⊢ X :: Z2 &
                               L ⊢ ⓑ{J}Y.Z2 ⬌* U.
/2 width=3/ qed-.                            

lemma ntaa_nta: ∀h,L,T,U. ⦃h, L⦄ ⊢ T :: U → ⦃h, L⦄ ⊢ T : U.
#h #L #T #U #H elim H -L -T -U
// /2 width=1/ /2 width=2/ /2 width=3/ /2 width=6/
qed-.

(* Properties on relocation *************************************************)

lemma ntaa_lift: ∀h,L1,T1,U1. ⦃h, L1⦄ ⊢ T1 :: U1 → ∀L2,d,e. ⇩[d, e] L2 ≡ L1 →
                 ∀T2. ⇧[d, e] T1 ≡ T2 → ∀U2. ⇧[d, e] U1 ≡ U2 → ⦃h, L2⦄ ⊢ T2 :: U2.
#h #L1 #T1 #U1 #H elim H -L1 -T1 -U1
[ #L1 #k #L2 #d #e #HL21 #X1 #H1 #X2 #H2
  >(lift_inv_sort1 … H1) -X1
  >(lift_inv_sort1 … H2) -X2 //
| #L1 #K1 #V1 #W1 #W #i #HLK1 #_ #HW1 #IHVW1 #L2 #d #e #HL21 #X #H #U2 #HWU2
  elim (lift_inv_lref1 … H) * #Hid #H destruct
  [ elim (lift_trans_ge … HW1 … HWU2 ?) -W // #W2 #HW12 #HWU2
    elim (ldrop_trans_le … HL21 … HLK1 ?) -L1 /2 width=2/ #X #HLK2 #H
    elim (ldrop_inv_skip2 … H ?) -H /2 width=1/ -Hid #K2 #V2 #HK21 #HV12 #H destruct
    /3 width=8/
  | lapply (lift_trans_be … HW1 … HWU2 ? ?) -W // /2 width=1/ #HW1U2
    lapply (ldrop_trans_ge … HL21 … HLK1 ?) -L1 // -Hid /3 width=8/
  ]
| #L1 #K1 #W1 #V1 #W #i #HLK1 #_ #HW1 #IHWV1 #L2 #d #e #HL21 #X #H #U2 #HWU2
  elim (lift_inv_lref1 … H) * #Hid #H destruct
  [ elim (lift_trans_ge … HW1 … HWU2 ?) -W // <minus_plus #W #HW1 #HWU2
    elim (ldrop_trans_le … HL21 … HLK1 ?) -L1 /2 width=2/ #X #HLK2 #H
    elim (ldrop_inv_skip2 … H ?) -H /2 width=1/ -Hid #K2 #W2 #HK21 #HW12 #H destruct
    lapply (lift_mono … HW1 … HW12) -HW1 #H destruct
    elim (lift_total V1 (d-i-1) e) /3 width=8/
  | lapply (lift_trans_be … HW1 … HWU2 ? ?) -W // /2 width=1/ #HW1U2
    lapply (ldrop_trans_ge … HL21 … HLK1 ?) -L1 // -Hid /3 width=8/
  ]
| #I #L1 #V1 #W1 #T1 #U1 #_ #_ #IHVW1 #IHTU1 #L2 #d #e #HL21 #X1 #H1 #X2 #H2
  elim (lift_inv_bind1 … H1) -H1 #V2 #T2 #HV12 #HT12 #H destruct
  elim (lift_inv_bind1 … H2) -H2 #X #U2 #H1 #HU12 #H2 destruct
  lapply (lift_mono … H1 … HV12) -H1 #H destruct
  elim (lift_total W1 d e) /4 width=6/
| #L1 #V1 #W1 #T1 #U1 #_ #_ #IHVW1 #IHTU1 #L2 #d #e #HL21 #X1 #H1 #X2 #H2
  elim (lift_inv_flat1 … H1) -H1 #V2 #X #HV12 #H1 #H destruct
  elim (lift_inv_bind1 … H1) -H1 #W2 #T2 #HW12 #HT12 #H destruct
  elim (lift_inv_flat1 … H2) -H2 #Y2 #X #HY #H2 #H destruct
  elim (lift_inv_bind1 … H2) -H2 #X2 #U2 #HX #HU12 #H destruct
  lapply (lift_mono … HY … HV12) -HY #H destruct
  lapply (lift_mono … HX … HW12) -HX #H destruct /4 width=6/
| #L1 #V1 #W1 #T1 #U1 #_ #_ #IHTU1 #IHUW1 #L2 #d #e #HL21 #X1 #H1 #X2 #H2
  elim (lift_inv_flat1 … H1) -H1 #V2 #T2 #HV12 #HT12 #H destruct
  elim (lift_inv_flat1 … H2) -H2 #X #U2 #H1 #HU12 #H2 destruct
  lapply (lift_mono … H1 … HV12) -H1 #H destruct
  elim (lift_total W1 d e) /4 width=6/
| #L1 #T1 #U1 #W1 #_ #_ #IHTU1 #IHUW1 #L2 #d #e #HL21 #X #H #U2 #HU12
  elim (lift_inv_flat1 … H) -H #X2 #T2 #HUX2 #HT12 #H destruct
  lapply (lift_mono … HUX2 … HU12) -HUX2 #H destruct
  elim (lift_total W1 d e) /3 width=6/
| #L1 #T1 #U11 #U12 #V12 #_ #HU112 #_ #IHTU11 #IHUV12 #L2 #d #e #HL21 #U1 #HTU1 #U2 #HU12
  elim (lift_total U11 d e) #U #HU11
  elim (lift_total V12 d e) #V22 #HV122
  lapply (cpcs_lift … HL21 … HU11 … HU12 HU112) -HU112 /3 width=6/
]
qed.

(* Advanced forvard lemmas **************************************************)

lemma ntaa_fwd_correct: ∀h,L,T,U. ⦃h, L⦄ ⊢ T :: U → ∃T0. ⦃h, L⦄ ⊢ U :: T0.
#h #L #T #U #H elim H -L -T -U
[ /2 width=2/
| #L #K #V #W #W0 #i #HLK #_ #HW0 * #V0 #HWV0
  lapply (ldrop_fwd_ldrop2 … HLK) -HLK #HLK
  elim (lift_total V0 0 (i+1)) /3 width=10/
| #L #K #W #V #V0 #i #HLK #HWV #HWV0 #_
  lapply (ldrop_fwd_ldrop2 … HLK) -HLK #HLK
  elim (lift_total V 0 (i+1)) /3 width=10/
| #I #L #V #W #T #U #HVW #_ #_ * /3 width=2/
| #L #V #W #T #U #HVW #_ #_ * #X #H
  elim (ntaa_inv_bind1 … H) -H /4 width=2/
| #L #V #W #T #U #_ #HUW * #T0 #HUT0 /3 width=2/
| /2 width=2/
| /2 width=2/
]
qed-.

(* Advanced properties ******************************************************)

lemma nta_ntaa: ∀h,L,T,U. ⦃h, L⦄ ⊢ T : U → ⦃h, L⦄ ⊢ T :: U.
#h #L #T #U #H elim H -L -T -U
// /2 width=1/ /2 width=2/ /2 width=3/ /2 width=6/
#L #T #U #_ #HTU
elim (ntaa_fwd_correct … HTU) /2 width=2/
qed.

(* Advanced eliminators *****************************************************)

lemma nta_ind_alt: ∀h. ∀R:lenv→relation term.
   (∀L,k. R L ⋆k ⋆(next h k)) →
   (∀L,K,V,W,U,i.
      ⇩[O, i] L ≡ K.ⓓV → ⦃h, K⦄ ⊢ V : W → ⇧[O, i + 1] W ≡ U →
      R K V W → R L (#i) U 
   ) →
   (∀L,K,W,V,U,i.
      ⇩[O, i] L ≡ K.ⓛW → ⦃h, K⦄ ⊢ W : V → ⇧[O, i + 1] W ≡ U →
      R K W V → R L (#i) U
   ) →
   (∀I,L,V,W,T,U.
      ⦃h, L⦄ ⊢ V : W → ⦃h, L.ⓑ{I}V⦄ ⊢ T : U →
      R L V W → R (L.ⓑ{I}V) T U → R L (ⓑ{I}V.T) (ⓑ{I}V.U)
   ) →
   (∀L,V,W,T,U.
      ⦃h, L⦄ ⊢ V : W → ⦃h, L⦄ ⊢ (ⓛW.T):(ⓛW.U) →
      R L V W →R L (ⓛW.T) (ⓛW.U) →R L (ⓐV.ⓛW.T) (ⓐV.ⓛW.U)
   ) →
   (∀L,V,W,T,U.
      ⦃h, L⦄ ⊢ T : U → ⦃h, L⦄ ⊢ (ⓐV.U) : W →
      R L T U → R L (ⓐV.U) W → R L (ⓐV.T) (ⓐV.U)
   ) →
   (∀L,T,U,W.
      ⦃h, L⦄ ⊢ T : U → ⦃h, L⦄ ⊢ U : W →
      R L T U → R L U W → R L (ⓝU.T) U
   ) →
   (∀L,T,U1,U2,V2.
      ⦃h, L⦄ ⊢ T : U1 → L ⊢ U1 ⬌* U2 → ⦃h, L⦄ ⊢ U2 : V2 →
      R L T U1 →R L U2 V2 →R L T U2
   ) →
   ∀L,T,U. ⦃h, L⦄ ⊢ T : U → R L T U.
#h #R #H1 #H2 #H3 #H4 #H5 #H6 #H7 #H8 #L #T #U #H elim (nta_ntaa … H) -L -T -U
// /3 width=1 by ntaa_nta/ /3 width=3 by ntaa_nta/ /3 width=4 by ntaa_nta/
/3 width=7 by ntaa_nta/
qed-.
