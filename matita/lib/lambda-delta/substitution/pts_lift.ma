(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic
    ||A||  Library of Mathematics, developed at the Computer Science
    ||T||  Department of the University of Bologna, Italy.
    ||I||
    ||T||
    ||A||  This file is distributed under the terms of the
    \   /  GNU General Public License Version 2
     \ /
      V_______________________________________________________________ *)

include "lambda-delta/substitution/lift_lift.ma".
include "lambda-delta/substitution/drop_drop.ma".
include "lambda-delta/substitution/pts.ma".

(* PARTIAL TELESCOPIC SUBSTITUTION ******************************************)

(* Relocation properties ****************************************************)

lemma pts_lift_le: ∀K,T1,T2,dt,et. K ⊢ T1 [dt, et] ≫ T2 →
                   ∀L,U1,U2,d,e. ↓[d, e] L ≡ K →
                   ↑[d, e] T1 ≡ U1 → ↑[d, e] T2 ≡ U2 →
                   dt + et ≤ d →
                   L ⊢ U1 [dt, et] ≫ U2.
#K #T1 #T2 #dt #et #H elim H -H K T1 T2 dt et
[ #K #k #dt #et #L #U1 #U2 #d #e #_ #H1 #H2 #_
  lapply (lift_mono … H1 … H2) -H1 H2 #H destruct -U1 //
| #K #i #dt #et #L #U1 #U2 #d #e #_ #H1 #H2 #_
  lapply (lift_mono … H1 … H2) -H1 H2 #H destruct -U1 //
| #K #KV #V #V1 #V2 #i #dt #et #Hdti #Hidet #HKV #_ #HV12 #IHV12 #L #U1 #U2 #d #e #HLK #H #HVU2 #Hdetd
  lapply (lt_to_le_to_lt … Hidet … Hdetd) #Hid
  lapply (lift_inv_lref1_lt … H … Hid) -H #H destruct -U1;
  elim (lift_trans_ge … HV12 … HVU2 ?) -HV12 HVU2 V2 // <minus_plus #V2 #HV12 #HVU2
  elim (drop_trans_le … HLK … HKV ?) -HLK HKV K /2/ #X #HLK #H
  elim (drop_inv_skip2 … H ?) -H /2/ -Hid #K #W #HKV #HVW #H destruct -X
  @pts_subst [4,5,6,8: // |1,2,3: skip | @IHV12 /2 width=6/ ] (**) (* explicit constructor *)
| #K #I #V1 #V2 #T1 #T2 #dt #et #_ #_ #IHV12 #IHT12 #L #U1 #U2 #d #e #HLK #H1 #H2 #Hdetd
  elim (lift_inv_bind1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1
  elim (lift_inv_bind1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct -U1 U2;
  @pts_bind [ /2 width=6/ | @IHT12 [3,4,5: /2/ |1,2: skip | /2/ ] ] (**) (* /3 width=6/ is too slow, arith3 needed to avoid crash *)
| #K #I #V1 #V2 #T1 #T2 #dt #et #_ #_ #IHV12 #IHT12 #L #U1 #U2 #d #e #HLK #H1 #H2 #Hdetd
  elim (lift_inv_flat1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1
  elim (lift_inv_flat1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct -U1 U2;
  /3 width=6/
]
qed.

lemma pts_lift_ge: ∀K,T1,T2,dt,et. K ⊢ T1 [dt, et] ≫ T2 →
                   ∀L,U1,U2,d,e. ↓[d, e] L ≡ K →
                   ↑[d, e] T1 ≡ U1 → ↑[d, e] T2 ≡ U2 →
                   d ≤ dt →
                   L ⊢ U1 [dt + e, et] ≫ U2.
#K #T1 #T2 #dt #et #H elim H -H K T1 T2 dt et
[ #K #k #dt #et #L #U1 #U2 #d #e #_ #H1 #H2 #_
  lapply (lift_mono … H1 … H2) -H1 H2 #H destruct -U1 //
| #K #i #dt #et #L #U1 #U2 #d #e #_ #H1 #H2 #_
  lapply (lift_mono … H1 … H2) -H1 H2 #H destruct -U1 //
| #K #KV #V #V1 #V2 #i #dt #et #Hdti #Hidet #HKV #HV1 #HV12 #_ #L #U1 #U2 #d #e #HLK #H #HVU2 #Hddt
  <(arith_c1x ? ? ? e) in HV1 #HV1 (**) (* explicit athmetical rewrite and ?'s *)
  lapply (transitive_le … Hddt … Hdti) -Hddt #Hid
  lapply (lift_inv_lref1_ge … H … Hid) -H #H destruct -U1;
  lapply (lift_trans_be … HV12 … HVU2 ? ?) -HV12 HVU2 V2 /2/ >plus_plus_comm_23 #HV1U2
  lapply (drop_trans_ge_comm … HLK … HKV ?) -HLK HKV K // -Hid #HLKV
  @pts_subst [4,5: /2/ |6,7,8: // |1,2,3: skip ] (**) (* /3 width=8/ is too slow *)
| #K #I #V1 #V2 #T1 #T2 #dt #et #_ #_ #IHV12 #IHT12 #L #U1 #U2 #d #e #HLK #H1 #H2 #Hddt
  elim (lift_inv_bind1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1
  elim (lift_inv_bind1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct -U1 U2;
  @pts_bind [ /2 width=5/ | /3 width=5/ ] (**) (* explicit constructor *)
| #K #I #V1 #V2 #T1 #T2 #dt #et #_ #_ #IHV12 #IHT12 #L #U1 #U2 #d #e #HLK #H1 #H2 #Hddt
  elim (lift_inv_flat1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1
  elim (lift_inv_flat1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct -U1 U2;
  /3 width=5/
]
qed.

lemma pts_inv_lift1_le: ∀L,U1,U2,dt,et. L ⊢ U1 [dt, et] ≫ U2 →
                        ∀K,d,e. ↓[d, e] L ≡ K → ∀T1. ↑[d, e] T1 ≡ U1 →
                        dt + et ≤ d →
                        ∃∃T2. K ⊢ T1 [dt, et] ≫ T2 & ↑[d, e] T2 ≡ U2.
#L #U1 #U2 #dt #et #H elim H -H L U1 U2 dt et
[ #L #k #dt #et #K #d #e #_ #T1 #H #_
  lapply (lift_inv_sort2 … H) -H #H destruct -T1 /2/
| #L #i #dt #et #K #d #e #_ #T1 #H #_
  elim (lift_inv_lref2 … H) -H * #Hid #H destruct -T1 /3/
| #L #KV #V #V1 #V2 #i #dt #et #Hdti #Hidet #HLKV #_ #HV12 #IHV12 #K #d #e #HLK #T1 #H #Hdetd
  lapply (lt_to_le_to_lt … Hidet … Hdetd) #Hid
  lapply (lift_inv_lref2_lt … H … Hid) -H #H destruct -T1;
  elim (drop_conf_lt … HLK … HLKV ?) -HLK HLKV L // #L #W #HKL #HKVL #HWV
  elim (IHV12 … HKVL … HWV ?) -HKVL HWV /2/ -Hdetd #W1 #HW1 #HWV1
  elim (lift_trans_le … HWV1 … HV12 ?) -HWV1 HV12 V1 // >arith_a2 /3 width=6/
| #L #I #V1 #V2 #U1 #U2 #dt #et #_ #_ #IHV12 #IHU12 #K #d #e #HLK #X #H #Hdetd
  elim (lift_inv_bind2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct -X;
  elim (IHV12 … HLK … HWV1 ?) -IHV12 //
  elim (IHU12 … HTU1 ?) -IHU12 HTU1 [3: /2/ |4: @drop_skip // |2: skip ] -HLK HWV1 Hdetd /3 width=5/ (**) (* just /3 width=5/ is too slow *)
| #L #I #V1 #V2 #U1 #U2 #dt #et #_ #_ #IHV12 #IHU12 #K #d #e #HLK #X #H #Hdetd
  elim (lift_inv_flat2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct -X;
  elim (IHV12 … HLK … HWV1 ?) -IHV12 HWV1 //
  elim (IHU12 … HLK … HTU1 ?) -IHU12 HLK HTU1 // /3 width=5/
]
qed.

lemma pts_inv_lift1_ge: ∀L,U1,U2,dt,et. L ⊢ U1 [dt, et] ≫ U2 →
                        ∀K,d,e. ↓[d, e] L ≡ K → ∀T1. ↑[d, e] T1 ≡ U1 →
                        d + e ≤ dt →
                        ∃∃T2. K ⊢ T1 [dt - e, et] ≫ T2 & ↑[d, e] T2 ≡ U2.
#L #U1 #U2 #dt #et #H elim H -H L U1 U2 dt et
[ #L #k #dt #et #K #d #e #_ #T1 #H #_
  lapply (lift_inv_sort2 … H) -H #H destruct -T1 /2/
| #L #i #dt #et #K #d #e #_ #T1 #H #_
  elim (lift_inv_lref2 … H) -H * #Hid #H destruct -T1 /3/
| #L #KV #V #V1 #V2 #i #dt #et #Hdti #Hidet #HLKV #HV1 #HV12 #_ #K #d #e #HLK #T1 #H #Hdedt
  lapply (transitive_le … Hdedt … Hdti) #Hdei
  lapply (plus_le_weak … Hdedt) -Hdedt #Hedt
  lapply (plus_le_weak … Hdei) #Hei
  <(arith_h1 ? ? ? e ? ?) in HV1 // #HV1
  lapply (lift_inv_lref2_ge … H … Hdei) -H #H destruct -T1;
  lapply (drop_conf_ge … HLK … HLKV ?) -HLK HLKV L // #HKV
  elim (lift_split … HV12 d (i - e + 1) ? ? ?) -HV12; [2,3,4: normalize /2/ ] -Hdei >arith_e2 // #V0 #HV10 #HV02
  @ex2_1_intro
  [2: @pts_subst [4: /2/ |6,7,8: // |1,2,3: skip |5: @arith5 // ]  
  |1: skip
  | //
  ] (**) (* explicitc constructors *)
| #L #I #V1 #V2 #U1 #U2 #dt #et #_ #_ #IHV12 #IHU12 #K #d #e #HLK #X #H #Hdetd
  elim (lift_inv_bind2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct -X;
  lapply (plus_le_weak … Hdetd) #Hedt
  elim (IHV12 … HLK … HWV1 ?) -IHV12 // #W2 #HW12 #HWV2
  elim (IHU12 … HTU1 ?) -IHU12 HTU1 [4: @drop_skip // |2: skip |3: /2/ ]
  <plus_minus // /3 width=5/
| #L #I #V1 #V2 #U1 #U2 #dt #et #_ #_ #IHV12 #IHU12 #K #d #e #HLK #X #H #Hdetd
  elim (lift_inv_flat2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct -X;
  elim (IHV12 … HLK … HWV1 ?) -IHV12 HWV1 //
  elim (IHU12 … HLK … HTU1 ?) -IHU12 HLK HTU1 // /3 width=5/
]
qed.

lemma pts_inv_lift1_eq: ∀L,U1,U2,d,e.
                        L ⊢ U1 [d, e] ≫ U2 → ∀T1. ↑[d, e] T1 ≡ U1 → U1 = U2.
#L #U1 #U2 #d #e #H elim H -H L U1 U2 d e
[ //
| //
| #L #K #V #V1 #V2 #i #d #e #Hdi #Hide #_ #_ #_ #_ #T1 #H
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
      Theorem subst0_gen_lift_ge : (u,t1,x:?; i,h,d:?) (subst0 i u (lift h d t1) x) ->
                                   (le (plus d h) i) ->
                                   (EX t2 | x = (lift h d t2) & (subst0 (minus i h) u t1 t2)).

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
