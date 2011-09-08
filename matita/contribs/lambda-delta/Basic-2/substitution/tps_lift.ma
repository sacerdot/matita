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

include "Basic-2/substitution/drop_drop.ma".
include "Basic-2/substitution/tps.ma".

(* PARTIAL SUBSTITUTION ON TERMS ********************************************)

(* Relocation properties ****************************************************)

(* Basic-1: was: subst1_lift_lt *)
lemma tps_lift_le: ∀K,T1,T2,dt,et. K ⊢ T1 [dt, et] ≫ T2 →
                   ∀L,U1,U2,d,e. ↓[d, e] L ≡ K →
                   ↑[d, e] T1 ≡ U1 → ↑[d, e] T2 ≡ U2 →
                   dt + et ≤ d →
                   L ⊢ U1 [dt, et] ≫ U2.
#K #T1 #T2 #dt #et #H elim H -H K T1 T2 dt et
[ #K #I #dt #et #L #U1 #U2 #d #e #_ #H1 #H2 #_
  >(lift_mono … H1 … H2) -H1 H2 //
| #K #KV #V #W #i #dt #et #Hdti #Hidet #HKV #HVW #L #U1 #U2 #d #e #HLK #H #HVU2 #Hdetd
  lapply (lt_to_le_to_lt … Hidet … Hdetd) -Hdetd #Hid
  lapply (lift_inv_lref1_lt … H … Hid) -H #H destruct -U1;
  elim (lift_trans_ge … HVW … HVU2 ?) -HVW HVU2 W // <minus_plus #W #HVW #HWU2
  elim (drop_trans_le … HLK … HKV ?) -HLK HKV K [2: /2/] #X #HLK #H
  elim (drop_inv_skip2 … H ?) -H [2: /2/] -Hid #K #Y #_ #HVY
  >(lift_mono … HVY … HVW) -HVY HVW Y #H destruct -X /2/
| #K #I #V1 #V2 #T1 #T2 #dt #et #_ #_ #IHV12 #IHT12 #L #U1 #U2 #d #e #HLK #H1 #H2 #Hdetd
  elim (lift_inv_bind1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1
  elim (lift_inv_bind1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct -U1 U2;
  @tps_bind [ /2 width=6/ | @IHT12 [3,4,5: /2/ |1,2: skip | /2/ ] ] (**) (* /3 width=6/ is too slow, arith3 needed to avoid crash *)
| #K #I #V1 #V2 #T1 #T2 #dt #et #_ #_ #IHV12 #IHT12 #L #U1 #U2 #d #e #HLK #H1 #H2 #Hdetd
  elim (lift_inv_flat1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1
  elim (lift_inv_flat1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct -U1 U2;
  /3 width=6/
]
qed.

(* Basic-1: was: subst1_lift_ge *)
lemma tps_lift_ge: ∀K,T1,T2,dt,et. K ⊢ T1 [dt, et] ≫ T2 →
                   ∀L,U1,U2,d,e. ↓[d, e] L ≡ K →
                   ↑[d, e] T1 ≡ U1 → ↑[d, e] T2 ≡ U2 →
                   d ≤ dt →
                   L ⊢ U1 [dt + e, et] ≫ U2.
#K #T1 #T2 #dt #et #H elim H -H K T1 T2 dt et
[ #K #I #dt #et #L #U1 #U2 #d #e #_ #H1 #H2 #_
  >(lift_mono … H1 … H2) -H1 H2 //
| #K #KV #V #W #i #dt #et #Hdti #Hidet #HKV #HVW #L #U1 #U2 #d #e #HLK #H #HWU2 #Hddt
  lapply (transitive_le … Hddt … Hdti) -Hddt #Hid
  lapply (lift_inv_lref1_ge … H … Hid) -H #H destruct -U1;
  lapply (lift_trans_be … HVW … HWU2 ? ?) -HVW HWU2 W // [ /2/ ] >plus_plus_comm_23 #HVU2
  lapply (drop_trans_ge_comm … HLK … HKV ?) -HLK HKV K // -Hid /3/
| #K #I #V1 #V2 #T1 #T2 #dt #et #_ #_ #IHV12 #IHT12 #L #U1 #U2 #d #e #HLK #H1 #H2 #Hddt
  elim (lift_inv_bind1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1
  elim (lift_inv_bind1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct -U1 U2;
  @tps_bind [ /2 width=5/ | /3 width=5/ ] (**) (* explicit constructor *)
| #K #I #V1 #V2 #T1 #T2 #dt #et #_ #_ #IHV12 #IHT12 #L #U1 #U2 #d #e #HLK #H1 #H2 #Hddt
  elim (lift_inv_flat1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1
  elim (lift_inv_flat1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct -U1 U2;
  /3 width=5/
]
qed.

(* Basic-1: was: subst1_gen_lift_lt *)
lemma tps_inv_lift1_le: ∀L,U1,U2,dt,et. L ⊢ U1 [dt, et] ≫ U2 →
                        ∀K,d,e. ↓[d, e] L ≡ K → ∀T1. ↑[d, e] T1 ≡ U1 →
                        dt + et ≤ d →
                        ∃∃T2. K ⊢ T1 [dt, et] ≫ T2 & ↑[d, e] T2 ≡ U2.
#L #U1 #U2 #dt #et #H elim H -H L U1 U2 dt et
[ #L * #i #dt #et #K #d #e #_ #T1 #H #_
  [ lapply (lift_inv_sort2 … H) -H #H destruct -T1 /2/
  | elim (lift_inv_lref2 … H) -H * #Hid #H destruct -T1 /3/
  ]
| #L #KV #V #W #i #dt #et #Hdti #Hidet #HLKV #HVW #K #d #e #HLK #T1 #H #Hdetd
  lapply (lt_to_le_to_lt … Hidet … Hdetd) -Hdetd #Hid
  lapply (lift_inv_lref2_lt … H … Hid) -H #H destruct -T1;
  elim (drop_conf_lt … HLK … HLKV ?) -HLK HLKV L // #L #U #HKL #_ #HUV
  elim (lift_trans_le … HUV … HVW ?) -HUV HVW V // >arith_a2 // -Hid /3/
| #L #I #V1 #V2 #U1 #U2 #dt #et #_ #_ #IHV12 #IHU12 #K #d #e #HLK #X #H #Hdetd
  elim (lift_inv_bind2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct -X;
  elim (IHV12 … HLK … HWV1 ?) -IHV12 HWV1 // #W2 #HW12 #HWV2
  elim (IHU12 … HTU1 ?) -IHU12 HTU1 [3: /2/ |4: @drop_skip // |2: skip ] -HLK Hdetd (**) (* /3 width=5/ is too slow *)
  /3 width=5/
| #L #I #V1 #V2 #U1 #U2 #dt #et #_ #_ #IHV12 #IHU12 #K #d #e #HLK #X #H #Hdetd
  elim (lift_inv_flat2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct -X;
  elim (IHV12 … HLK … HWV1 ?) -IHV12 HWV1 //
  elim (IHU12 … HLK … HTU1 ?) -IHU12 HLK HTU1 // /3 width=5/
]
qed.

(* Basic-1: was: subst1_gen_lift_ge *)
lemma tps_inv_lift1_ge: ∀L,U1,U2,dt,et. L ⊢ U1 [dt, et] ≫ U2 →
                        ∀K,d,e. ↓[d, e] L ≡ K → ∀T1. ↑[d, e] T1 ≡ U1 →
                        d + e ≤ dt →
                        ∃∃T2. K ⊢ T1 [dt - e, et] ≫ T2 & ↑[d, e] T2 ≡ U2.
#L #U1 #U2 #dt #et #H elim H -H L U1 U2 dt et
[ #L * #i #dt #et #K #d #e #_ #T1 #H #_
  [ lapply (lift_inv_sort2 … H) -H #H destruct -T1 /2/
  | elim (lift_inv_lref2 … H) -H * #Hid #H destruct -T1 /3/
  ]
| #L #KV #V #W #i #dt #et #Hdti #Hidet #HLKV #HVW #K #d #e #HLK #T1 #H #Hdedt  
  lapply (transitive_le … Hdedt … Hdti) #Hdei
  lapply (plus_le_weak … Hdedt) -Hdedt #Hedt
  lapply (plus_le_weak … Hdei) #Hei  
  lapply (lift_inv_lref2_ge … H … Hdei) -H #H destruct -T1;
  lapply (drop_conf_ge … HLK … HLKV ?) -HLK HLKV L // #HKV
  elim (lift_split … HVW d (i - e + 1) ? ? ?) -HVW; [2,3,4: normalize /2/ ] -Hdei >arith_e2 // #V0 #HV10 #HV02
  @ex2_1_intro
  [2: @tps_subst [3: /2/ |5,6: // |1,2: skip |4: @arith5 // ]
  |1: skip
  | //
  ] (**) (* explicitc constructors *)
| #L #I #V1 #V2 #U1 #U2 #dt #et #_ #_ #IHV12 #IHU12 #K #d #e #HLK #X #H #Hdetd
  elim (lift_inv_bind2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct -X;
  lapply (plus_le_weak … Hdetd) #Hedt
  elim (IHV12 … HLK … HWV1 ?) -IHV12 HWV1 // #W2 #HW12 #HWV2
  elim (IHU12 … HTU1 ?) -IHU12 HTU1 [4: @drop_skip // |2: skip |3: /2/ ]
  <plus_minus // /3 width=5/
| #L #I #V1 #V2 #U1 #U2 #dt #et #_ #_ #IHV12 #IHU12 #K #d #e #HLK #X #H #Hdetd
  elim (lift_inv_flat2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct -X;
  elim (IHV12 … HLK … HWV1 ?) -IHV12 HWV1 //
  elim (IHU12 … HLK … HTU1 ?) -IHU12 HLK HTU1 // /3 width=5/
]
qed.

(* Basic-1: was: subst1_gen_lift_eq *)
lemma tps_inv_lift1_eq: ∀L,U1,U2,d,e.
                        L ⊢ U1 [d, e] ≫ U2 → ∀T1. ↑[d, e] T1 ≡ U1 → U1 = U2.
#L #U1 #U2 #d #e #H elim H -H L U1 U2 d e
[ //
| #L #K #V #W #i #d #e #Hdi #Hide #_ #_ #T1 #H
  elim (lift_inv_lref2 … H) -H * #H
  [ lapply (le_to_lt_to_lt … Hdi … H) -Hdi H #H
    elim (lt_refl_false … H)
  | lapply (lt_to_le_to_lt … Hide … H) -Hide H #H
    elim (lt_refl_false … H)
  ]
| #L #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #X #HX
  elim (lift_inv_bind2 … HX) -HX #V #T #HV1 #HT1 #H destruct -X
  >IHV12 // >IHT12 //
| #L #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #X #HX
  elim (lift_inv_flat2 … HX) -HX #V #T #HV1 #HT1 #H destruct -X
  >IHV12 // >IHT12 //
]
qed.
(*
      Theorem subst0_gen_lift_rev_ge: (t1,v,u2:?; i,h,d:?) 
                                      (subst0 i v t1 (lift h d u2)) ->
                                      (le (plus d h) i) ->
                                      (EX u1 | (subst0 (minus i h) v u1 u2) &
		                               t1 = (lift h d u1)
		                      ).


      Theorem subst0_gen_lift_rev_lelt: (t1,v,u2:?; i,h,d:?)
                                        (subst0 i v t1 (lift h d u2)) ->
                                        (le d i) -> (lt i (plus d h)) ->
				        (EX u1 | t1 = (lift (minus (plus d h) (S i)) (S i) u1)).
*)

lemma tps_inv_lift1_up: ∀L,U1,U2,dt,et. L ⊢ U1 [dt, et] ≫ U2 →
                        ∀K,d,e. ↓[d, e] L ≡ K → ∀T1. ↑[d, e] T1 ≡ U1 →
                        d ≤ dt → dt ≤ d + e → d + e ≤ dt + et →
                        ∃∃T2. K ⊢ T1 [d, dt + et - (d + e)] ≫ T2 & ↑[d, e] T2 ≡ U2.
#L #U1 #U2 #dt #et #HU12 #K #d #e #HLK #T1 #HTU1 #Hddt #Hdtde #Hdedet
elim (tps_split_up … HU12 (d + e) ? ?) -HU12 // -Hdedet #U #HU1 #HU2
lapply (tps_weak … HU1 d e ? ?) -HU1 // <plus_minus_m_m_comm // -Hddt Hdtde #HU1
lapply (tps_inv_lift1_eq … HU1 … HTU1) -HU1 #HU1 destruct -U1;
elim (tps_inv_lift1_ge … HU2 … HLK … HTU1 ?) -HU2 HLK HTU1 // <minus_plus_m_m /2/
qed.

(* Advanced inversion lemmas ************************************************)

fact tps_inv_refl_SO2_aux: ∀L,T1,T2,d,e. L ⊢ T1 [d, e] ≫ T2 → e = 1 →
                           ∀K,V. ↓[0, d] L ≡ K. 𝕓{Abst} V → T1 = T2.
#L #T1 #T2 #d #e #H elim H -H L T1 T2 d e
[ //
| #L #K0 #V0 #W #i #d #e #Hdi #Hide #HLK0 #_ #H destruct -e;
  >(le_to_le_to_eq … Hdi ?) /2/ -d #K #V #HLK
  lapply (drop_mono … HLK0 … HLK) #H destruct
| #L #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #H1 #K #V #HLK
  >(IHV12 H1 … HLK) -IHV12 >(IHT12 H1 K V) -IHT12 /2/
| #L #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #H1 #K #V #HLK
  >(IHV12 H1 … HLK) -IHV12 >(IHT12 H1 … HLK) -IHT12 //
]
qed.

lemma tps_inv_refl_SO2: ∀L,T1,T2,d. L ⊢ T1 [d, 1] ≫ T2 →
                        ∀K,V. ↓[0, d] L ≡ K. 𝕓{Abst} V → T1 = T2.
/2 width=8/ qed.
