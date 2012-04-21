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

(* Advanced inversion lemmas ************************************************)

fact nta_inv_sort1_aux: ∀h,L,T,U. ⦃h, L⦄ ⊢ T : U → ∀k0. T = ⋆k0 →
                        L ⊢ ⋆(next h k0) ⬌* U.
#h #L #T #U #H elim H -L -T -U
[ #L #k #k0 #H destruct //
| #L #K #V #W #U #i #_ #_ #_ #_ #k0 #H destruct
| #L #K #W #V #U #i #_ #_ #_ #_ #k0 #H destruct
| #I #L #V #W #T #U #_ #_ #_ #_ #k0 #H destruct
| #L #V #W #U #T1 #T2 #_ #_ #_ #_ #_ #_ #k0 #H destruct
| #L #V #W #T #U #_ #_ #_ #_ #k0 #H destruct
| #L #T #U #_ #_ #k0 #H destruct
| #L #T #U1 #U2 #V2 #_ #HU12 #_ #IHTU1 #_ #k0 #H destruct
  lapply (IHTU1 ??) -IHTU1 [ // | skip ] #Hk0
  lapply (cpcs_trans … Hk0 … HU12) -U1 //
]
qed.

(* Basic_1: was: ty3_gen_sort *)
lemma nta_inv_sort1: ∀h,L,U,k. ⦃h, L⦄ ⊢ ⋆k : U → L ⊢ ⋆(next h k) ⬌* U.
/2 width=3/ qed-.

fact nta_inv_lref1_aux: ∀h,L,T,U. ⦃h, L⦄ ⊢ T : U → ∀j. T = #j →
                        (∃∃K,V,W,U0. ⇩[0, j] L ≡ K. ⓓV & ⦃h, K⦄ ⊢ V : W &
                                     ⇧[0, j + 1] W ≡ U0 & L ⊢ U0 ⬌* U
                        ) ∨
                        (∃∃K,W,V,U0. ⇩[0, j] L ≡ K. ⓛW & ⦃h, K⦄ ⊢ W : V &
                                     ⇧[0, j + 1] W ≡ U0 & L ⊢ U0 ⬌* U
                        ).
#h #L #T #U #H elim H -L -T -U
[ #L #k #j #H destruct
| #L #K #V #W #U #i #HLK #HVW #HWU #_ #j #H destruct /3 width=8/
| #L #K #W #V #U #i #HLK #HWV #HWU #_ #j #H destruct /3 width=8/
| #I #L #V #W #T #U #_ #_ #_ #_ #j #H destruct
| #L #V #W #U #T1 #T2 #_ #_ #_ #_ #_ #_ #j #H destruct
| #L #V #W #T #U #_ #_ #_ #_ #j #H destruct
| #L #T #U #_ #_ #j #H destruct
| #L #T #U1 #U2 #V2 #_ #HU12 #_ #IHTU1 #_ #j #H destruct
  elim (IHTU1 ??) -IHTU1 [4: // |2: skip ] * #K #V #W #U0 #HLK #HVW #HWU0 #HU01
  lapply (cpcs_trans … HU01 … HU12) -U1 /3 width=8/
]
qed.

(* Basic_1: was ty3_gen_lref *)
lemma nta_inv_lref1: ∀h,L,U,i. ⦃h, L⦄ ⊢ #i : U →
                     (∃∃K,V,W,U0. ⇩[0, i] L ≡ K. ⓓV & ⦃h, K⦄ ⊢ V : W &
                                  ⇧[0, i + 1] W ≡ U0 & L ⊢ U0 ⬌* U
                     ) ∨
                     (∃∃K,W,V,U0. ⇩[0, i] L ≡ K. ⓛW & ⦃h, K⦄ ⊢ W : V &
                                  ⇧[0, i + 1] W ≡ U0 & L ⊢ U0 ⬌* U
                     ).
/2 width=3/ qed-.

fact nta_inv_bind1_aux: ∀h,L,T,U. ⦃h, L⦄ ⊢ T : U → ∀J,X,Y. T = ⓑ{J}Y.X →
                        ∃∃Z1,Z2. ⦃h, L⦄ ⊢ Y : Z1 & ⦃h, L.ⓑ{J}Y⦄ ⊢ X : Z2 &
                                 L ⊢ ⓑ{J}Y.Z2 ⬌* U.
#h #L #T #U #H elim H -L -T -U
[ #L #k #J #X #Y #H destruct
| #L #K #V #W #U #i #_ #_ #_ #_ #J #X #Y #H destruct
| #L #K #W #V #U #i #_ #_ #_ #_ #J #X #Y #H destruct
| #I #L #V #W #T #U #HVW #HTU #_ #_ #J #X #Y #H destruct /2 width=3/
| #L #V #W #U #T1 #T2 #_ #_ #_ #_ #_ #_ #J #X #Y #H destruct
| #L #V #W #T #U #_ #_ #_ #_ #J #X #Y #H destruct
| #L #T #U #_ #_ #J #X #Y #H destruct
| #L #T #U1 #U2 #V2 #_ #HU12 #_ #IHTU1 #_ #J #X #Y #H destruct
  elim (IHTU1 ????) -IHTU1 [5: // |2,3,4: skip ] #Z1 #Z2 #HZ1 #HZ2 #HU1
  lapply (cpcs_trans … HU1 … HU12) -U1 /2 width=3/
]
qed.

(* Basic_1: was: ty3_gen_bind *)
lemma nta_inv_bind1: ∀h,J,L,Y,X,U. ⦃h, L⦄ ⊢ ⓑ{J}Y.X : U →
                     ∃∃Z1,Z2. ⦃h, L⦄ ⊢ Y : Z1 & ⦃h, L.ⓑ{J}Y⦄ ⊢ X : Z2 &
                              L ⊢ ⓑ{J}Y.Z2 ⬌* U.
/2 width=3/ qed-.                            

fact nta_inv_cast1_aux: ∀h,L,T,U. ⦃h, L⦄ ⊢ T : U → ∀X,Y. T = ⓣY.X →
                     ⦃h, L⦄ ⊢ X : Y ∧ L ⊢ Y ⬌* U.
#h #L #T #U #H elim H -L -T -U
[ #L #k #X #Y #H destruct
| #L #K #V #W #U #i #_ #_ #_ #_ #X #Y #H destruct
| #L #K #W #V #U #i #_ #_ #_ #_ #X #Y #H destruct
| #I #L #V #W #T #U #_ #_ #_ #_ #X #Y #H destruct
| #L #V #W #U #T1 #T2 #_ #_ #_ #_ #_ #_ #X #Y #H destruct
| #L #V #W #T #U #_ #_ #_ #_ #X #Y #H destruct
| #L #T #U #HTU #_ #X #Y #H destruct /2 width=1/
| #L #T #U1 #U2 #V2 #_ #HU12 #_ #IHTU1 #_ #X #Y #H destruct
  elim (IHTU1 ???) -IHTU1 [4: // |2,3: skip ] #HXY #HU1
  lapply (cpcs_trans … HU1 … HU12) -U1 /2 width=1/
]
qed.

(* Basic_1: was: ty3_gen_cast *)
lemma nta_inv_cast1: ∀h,L,X,Y,U. ⦃h, L⦄ ⊢ ⓣY.X : U →  ⦃h, L⦄ ⊢ X : Y ∧ L ⊢ Y ⬌* U.
/2 width=3/ qed-.

(* Properties on relocation *************************************************)

(* Basic_1: was: ty3_lift *)
lemma nta_lift: ∀h,L1,T1,U1. ⦃h, L1⦄ ⊢ T1 : U1 → ∀L2,d,e. ⇩[d, e] L2 ≡ L1 →
                ∀T2. ⇧[d, e] T1 ≡ T2 → ∀U2. ⇧[d, e] U1 ≡ U2 → ⦃h, L2⦄ ⊢ T2 : U2.
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
| #L1 #V1 #W1 #U1 #T11 #T12 #_ #_ #_ #IHVW1 #IHWU1 #IHT112 #L2 #d #e #HL21 #X1 #H1 #X2 #H2
  elim (lift_inv_flat1 … H1) -H1 #V2 #X #HV12 #H1 #H destruct
  elim (lift_inv_bind1 … H1) -H1 #W2 #T12 #HW12 #HT112 #H destruct
  elim (lift_inv_flat1 … H2) -H2 #X0 #X #H0 #H2 #H destruct
  elim (lift_inv_bind1 … H2) -H2 #Y0 #T22 #H2 #HT122 #H destruct
  lapply (lift_mono … H0 … HV12) -H0 #H destruct
  lapply (lift_mono … H2 … HW12) -H2 #H destruct
  elim (lift_total U1 d e) #U2 #HU12
  @nta_appl [2,3: /2 width=5/ | skip | /3 width=5/ ] (**) (* explicit constructor, /4 width=6/ is too slow *)
| #L1 #V1 #W1 #T1 #U1 #_ #_ #IHTU1 #IHUW1 #L2 #d #e #HL21 #X1 #H1 #X2 #H2
  elim (lift_inv_flat1 … H1) -H1 #V2 #T2 #HV12 #HT12 #H destruct
  elim (lift_inv_flat1 … H2) -H2 #X #U2 #H1 #HU12 #H2 destruct
  lapply (lift_mono … H1 … HV12) -H1 #H destruct
  elim (lift_total W1 d e) /4 width=6/
| #L1 #T1 #U1 #_ #IHTU1 #L2 #d #e #HL21 #X #H #U2 #HU12
  elim (lift_inv_flat1 … H) -H #X2 #T2 #HUX2 #HT12 #H destruct
  lapply (lift_mono … HUX2 … HU12) -HUX2 #H destruct /3 width=5/
| #L1 #T1 #U11 #U12 #V12 #_ #HU112 #_ #IHTU11 #IHUV12 #L2 #d #e #HL21 #U1 #HTU1 #U2 #HU12
  elim (lift_total U11 d e) #U #HU11
  elim (lift_total V12 d e) #V22 #HV122
  lapply (cpcs_lift … HL21 … HU11 … HU12 HU112) -HU112 /3 width=6/
]
qed.

(* Advanced forvard lemmas **************************************************)

(* Basic_1: was: ty3_correct *)
lemma nta_fwd_correct: ∀h,L,T,U. ⦃h, L⦄ ⊢ T : U → ∃T0. ⦃h, L⦄ ⊢ U : T0.
#h #L #T #U #H elim H -L -T -U
[ /2 width=2/
| #L #K #V #W #W0 #i #HLK #_ #HW0 * #V0 #HWV0
  lapply (ldrop_fwd_ldrop2 … HLK) -HLK #HLK
  elim (lift_total V0 0 (i+1)) /3 width=10/
| #L #K #W #V #V0 #i #HLK #HWV #HWV0 #_
  lapply (ldrop_fwd_ldrop2 … HLK) -HLK #HLK
  elim (lift_total V 0 (i+1)) /3 width=10/
| #I #L #V #W #T #U #HVW #_ #_ * /3 width=2/
| #L #V #W #U #T1 #T2 #HVW #HWU #_ #_ #_ * /3 width=2/
| #L #V #W #T #U #_ #HUW * #T0 #HUT0 /3 width=2/
| #L #T #U #_ * /2 width=2/
| /2 width=2/
]
qed-.

(* Advanced properties ******************************************************)

(* Basic_1: was: ty3_appl *)
lemma nta_appl_old: ∀h,L,V,W,T,U. ⦃h, L⦄ ⊢ V : W → ⦃h, L⦄ ⊢ T : ⓛW.U →
                    ⦃h, L⦄ ⊢ ⓐV.T : ⓐV.ⓛW.U.
#h #L #V #W #T #U #HVW #HTU
elim (nta_fwd_correct … HTU) #X #H
elim (nta_inv_bind1 … H) -H #V0 #T0 #HWV0 #HUT0 #_ -X /3 width=2/
qed.
