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
include "basic_2/unfold/thin_ldrop.ma".
include "basic_2/equivalence/cpcs_delift.ma".
include "basic_2/dynamic/nta_nta.ma".

(* NATIVE TYPE ASSIGNMENT ON TERMS ******************************************)

(* Properties on reverse basic term relocation ******************************)

(* Basic_1: was only: ty3_gen_cabbr *)
axiom thin_nta_delift_conf: ∀h,L1,T1,X1. ⦃h, L1⦄ ⊢ T1 : X1 →
                            ∀L2,d,e. L1 [d, e] ≡ L2 →
                            ∀T2. L1 ⊢ T1 [d, e] ≡ T2 →
                            ∃∃U1,U2. ⦃h, L2⦄ ⊢ T2 : U2 & L1 ⊢ U1 [d, e] ≡ U2 &
                                     L1 ⊢ U1 ⬌* X1.
(*
#h #L1 #T1 #U1 #H @(nta_ind_alt … H) -L1 -T1 -U1
[ #L1 #k #L2 #d #e #HL12 #X #H
  >(delift_inv_sort1 … H) -X /2 width=5/
| #L1 #K1 #V1 #W1 #U1 #i #HLK1 #_ #HWU1 #IHVW1 #L2 #d #e #HL12 #X #H
(*
  elim (delift_inv_lref1 … H) -H *
  [ #Hid #H destruct
    elim (thin_ldrop_conf_le … HL12 … HLK1 ?) -HL12 /2 width=2/ #X #H #HLK2
    lapply (ldrop_fwd_ldrop2 … HLK1) -HLK1 #HLK1
    elim (thin_inv_delift1 … H ?) -H /2 width=1/ #K2 #V2 #HK12 #HV12 #H destruct
    elim (IHVW1 … HK12 … HV12) -IHVW1 -HK12 -HV12 #W2 #HVW2 #HW12
    elim (lift_total W2 0 (i+1)) #U2 #HWU2
    @(ex2_1_intro … U2)
    [ /2 width=6/
    | -HVW2 -HLK2 
    ]
  |
  |
  ]
*)
|
|
|
| #L1 #V1 #W1 #T1 #U1 #_ #_ #IHTU1 #IHVW1 #L2 #d #e #HL12 #X #H
  elim (delift_inv_flat1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
(*  
  elim (IHTU1 … HL12 … HT12) -T1 #U2 #HTU2 #HU12
  elim (IHVW1 … HL12 (ⓐV2.U2) ?) -IHVW1 -HL12
  [ /3 width=5/ | /2 width=1/ ]
*)
| #L1 #T1 #X1 #Y1 #_ #_ #IHTX1 #IHXY1 #L2 #d #e #HL12 #X #H
  elim (delift_inv_flat1 … H) -H #X2 #T2 #HX12 #HT12 #H destruct
  elim (IHTX1 … HL12 … HT12) -T1 #U1 #U2 #HTU2 #HU12 #HUX1
  elim (IHXY1 … HL12 … HX12) -IHXY1 #W1 #W2 #HXW2 #_ #_ -Y1 -W1
  lapply (thin_cpcs_delift_mono … HUX1 … HL12 … HU12 … HX12) -HL12 -HX12 /4 width=5/
| #L1 #T1 #X11 #X12 #V1 #_ #HX112 #_ #IHT1 #_ #L2 #d #e #HL12 #T2 #HT12
  elim (IHT1 … HL12 … HT12) -T1 -HL12 #U21 #U22 #HTU22 #HU212 #HUX211
  lapply (cpcs_trans … HUX211 … HX112) -X11 /2 width=5/
]
*)
lemma nta_inv_lift1_delift: ∀h,L1,T1,X. ⦃h, L1⦄ ⊢ T1 : X →
                            ∀L2,d,e. ⇩[d, e] L1 ≡ L2 → ∀T2. ⇧[d, e] T2 ≡ T1 →
                            ∃∃U1,U2. ⦃h, L2⦄ ⊢ T2 : U2 & L1 ⊢ U1 [d, e] ≡ U2 &
                                     L1 ⊢ U1 ⬌* X.
/3 width=3/ qed-.

lemma nta_inv_lift1: ∀h,L1,T1,X. ⦃h, L1⦄ ⊢ T1 : X →
                     ∀L2,d,e. ⇩[d, e] L1 ≡ L2 → ∀T2. ⇧[d, e] T2 ≡ T1 →
                     ∃∃U1,U2. ⦃h, L2⦄ ⊢ T2 : U2 & ⇧[d, e] U2 ≡ U1 &
                              L1 ⊢ U1 ⬌* X.
#h #L1 #T1 #X #H #L2 #d #e #HL12 #T2 #HT21
elim (nta_inv_lift1_delift … H … HL12 … HT21) -T1 -HL12 #U1 #U2 #HTU2 * #U #HU1 #HU2 #HU1X
lapply (cpcs_cpr_conf … U … HU1X) -HU1X /2 width=3/ -U1 /2 width=5/
qed-.
