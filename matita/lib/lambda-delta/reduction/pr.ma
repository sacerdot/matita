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

include "lambda-delta/substitution/thin.ma".

(* SINGLE STEP PARALLEL REDUCTION *******************************************)

inductive pr: lenv → term → term → Prop ≝
| pr_sort : ∀L,k. pr L (⋆k) (⋆k)
| pr_lref : ∀L,i. pr L (#i) (#i)
| pr_bind : ∀L,I,V1,V2,T1,T2. pr L V1 V2 → pr (L. 𝕓{I} V1) T1 T2 →
            pr L (𝕓{I} V1. T1) (𝕓{I} V2. T2)
| pr_flat : ∀L,I,V1,V2,T1,T2. pr L V1 V2 → pr L T1 T2 →
            pr L (𝕗{I} V1. T1) (𝕗{I} V2. T2)
| pr_beta : ∀L,V1,V2,W,T1,T2.
            pr L V1 V2 → pr (L. 𝕓{Abst} W) T1 T2 → (*𝕓*)
            pr L (𝕚{Appl} V1. 𝕚{Abst} W. T1) (𝕚{Abbr} V2. T2)
| pr_delta: ∀L,K,V1,V2,V,i.
            ↓[0,i] L ≡ K. 𝕓{Abbr} V1 → pr K V1 V2 → ↑[0,i+1] V2 ≡ V →
            pr L (#i) V
| pr_theta: ∀L,V,V1,V2,W1,W2,T1,T2.
            pr L V1 V2 → ↑[0,1] V2 ≡ V → pr L W1 W2 → pr (L. 𝕓{Abbr} W1) T1 T2 → (*𝕓*)
            pr L (𝕚{Appl} V1. 𝕚{Abbr} W1. T1) (𝕚{Abbr} W2. 𝕚{Appl} V. T2)
| pr_zeta : ∀L,V,T,T1,T2. ↑[0,1] T1 ≡ T → pr L T1 T2 →
            pr L (𝕚{Abbr} V. T) T2
| pr_tau  : ∀L,V,T1,T2. pr L T1 T2 → pr L (𝕚{Cast} V. T1) T2
.

interpretation "single step parallel reduction" 'PR L T1 T2 = (pr L T1 T2).

(* The three main lemmas on reduction ***************************************)

lemma pr_inv_lift: ∀L,T1,T2. L ⊢ T1 ⇒ T2 →
                   ∀d,e,K. ↓[d,e] L ≡ K → ∀U1. ↑[d,e] U1 ≡ T1 →
                   ∃∃U2. ↑[d,e] U2 ≡ T2 & K ⊢ U1 ⇒ U2.
#L #T1 #T2 #H elim H -H L T1 T2
[ #L #k #d #e #K #_ #U1 #HU1
  lapply (lift_inv_sort2 … HU1) -HU1 #H destruct -U1 /2/
| #L #i #d #e #K #_ #U1 #HU1
  lapply (lift_inv_lref2 … HU1) -HU1 * * #Hid #H destruct -U1 /3/
| #L #I #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #d #e #K #HLK #X #HX
  lapply (lift_inv_bind2 … HX) -HX * #V0 #T0 #HV01 #HT01 #HX destruct -X;
  elim (IHV12 … HLK … HV01) -IHV12 #V3 #HV32 #HV03
  elim (IHT12 … HT01) -IHT12 HT01 [2,3: -HV32 HV03 /3/] -HLK HV01 /3 width=5/
| #L #I #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #d #e #K #HLK #X #HX
  elim (lift_inv_flat2 … HX) -HX #V0 #T0 #HV01 #HT01 #HX destruct -X;
  elim (IHV12 … HLK … HV01) -IHV12 HV01 #V3 #HV32 #HV03
  elim (IHT12 … HLK … HT01) -IHT12 HT01 HLK /3 width=5/
| #L #V1 #V2 #W1 #T1 #T2 #_ #_ #IHV12 #IHT12 #d #e #K #HLK #X #HX
  elim (lift_inv_flat2 … HX) -HX #V0 #Y #HV01 #HY #HX destruct -X;
  elim (lift_inv_bind2 … HY) -HY #W0 #T0 #HW01 #HT01 #HY destruct -Y;
  elim (IHV12 … HLK … HV01) -IHV12 HV01 #V3 #HV32 #HV03
  elim (IHT12 … HT01) -IHT12 HT01
    [3: -HV32 HV03 @(thin_skip … HLK) /2/ |2: skip ] (**) (* /3 width=5/ is too slow *)
    -HLK HW01
  /3 width=5/
| #L #K0 #V1 #V2 #V0 #i #HLK0 #HV12 #HV20 #IHV12 #d #e #K #HLK #X #HX
  lapply (lift_inv_lref2 … HX) -HX * * #Hid #HX destruct -X;
  [ -HV12;
    elim (thin_conf_lt … HLK … HLK0 Hid) -HLK HLK0 L #L #V3 #HKL #HK0L #HV31
    elim (IHV12 … HK0L … HV31) -IHV12 HK0L HV31 #V4 #HV42 #HV34
    elim (lift_trans_le … HV42 … HV20 ?) -HV42 HV20 V2 // #V2 #HV42
    >arith5 // -Hid #HV20  
    @(ex2_1_intro … V2) /2 width=6/ (**) (* /3 width=8/ is slow *)
  | -IHV12;
    lapply (thin_conf_ge … HLK … HLK0 Hid) -HLK HLK0 L #HK
    elim (lift_free … HV20 d (i - e + 1) ? ? ?) -HV20 /2/
    >arith3 /2/ -Hid /3 width=8/ (**) (* just /3 width=8/ is a bit slow *)
  ]
| #L #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #HV2 #_ #_ #IHV12 #IHW12 #IHT12 #d #e #K #HLK #X #HX
  elim (lift_inv_flat2 … HX) -HX #V0 #Y #HV01 #HY #HX destruct -X;
  elim (lift_inv_bind2 … HY) -HY #W0 #T0 #HW01 #HT01 #HY destruct -Y;
  elim (IHV12 ? ? ? HLK ? HV01) -IHV12 HV01 #V3 #HV32 #HV03
  elim (IHW12 ? ? ? HLK ? HW01) -IHW12 #W3 #HW32 #HW03
  elim (IHT12 … HT01) -IHT12 HT01
    [3: -HV2 HV32 HV03 HW32 HW03 @(thin_skip … HLK) /2/ |2: skip ] (**) (* /3/ is too slow *)
    -HLK HW01 #T3 #HT32 #HT03
  elim (lift_trans_le … HV32 … HV2 ?) -HV32 HV2 V2 // #V2 #HV32 #HV2
  @(ex2_1_intro … (𝕓{Abbr}W3.𝕗{Appl}V2.T3)) /3/ (**) (* /4/ loops *)
| #L #V #T #T1 #T2 #HT1 #_ #IHT12 #d #e #K #HLK #X #HX
  elim (lift_inv_bind2 … HX) -HX #V0 #T0 #_ #HT0 #H destruct -X;
  elim (lift_conf_rev … HT1 … HT0 ?) -HT1 HT0 T // #T #HT0 #HT1
  elim (IHT12 … HLK … HT1) -IHT12 HLK HT1 /3 width=5/
| #L #V #T1 #T2 #_ #IHT12 #d #e #K #HLK #X #HX
  elim (lift_inv_flat2 … HX) -HX #V0 #T0 #_ #HT01 #H destruct -X;
  elim (IHT12 … HLK … HT01) -IHT12 HLK HT01 /3/
]
qed.

(* this may be moved *)
lemma pr_refl: ∀T,L. L ⊢ T ⇒ T.
#T elim T -T //
#I elim I -I /2/
qed.
