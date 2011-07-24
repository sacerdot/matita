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

(*
include "lambda-delta/substitution/lift_fun.ma".
include "lambda-delta/substitution/lift_main.ma".
include "lambda-delta/substitution/drop_main.ma".
*)
include "lambda-delta/reduction/tpr_defs.ma".

axiom tpr_lift: ∀T1,T2. T1 ⇒ T2 →
                ∀d,e,U1. ↑[d, e] T1 ≡ U1 → ∀U2. ↑[d, e] T2 ≡ U2 → U1 ⇒ U2.
(*
#L #T1 #T2 #H elim H -H L T1 T2
[ #L #k #d #e #K #_ #U1 #HU1 #U2 #HU2
  lapply (lift_mono … HU1 … HU2) -HU1 #H destruct -U1; 
  lapply (lift_inv_sort1 … HU2) -HU2 #H destruct -U2 //
| #L #i #d #e #K #_ #U1 #HU1 #U2 #HU2
  lapply (lift_mono … HU1 … HU2) -HU1 #H destruct -U1;
  lapply (lift_inv_lref1 … HU2) * * #Hid #H destruct -U2 //
| #L #I #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #d #e #K #HKL #X1 #HX1 #X2 #HX2
  elim (lift_inv_bind1 … HX1) -HX1 #W1 #U1 #HVW1 #HTU1 #HX1 destruct -X1;
  elim (lift_inv_bind1 … HX2) -HX2 #W2 #U2 #HVW2 #HTU2 #HX2 destruct -X2
  /5 width=5/
| #L #I #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #d #e #K #HKL #X1 #HX1 #X2 #HX2
  elim (lift_inv_flat1 … HX1) -HX1 #W1 #U1 #HVW1 #HTU1 #HX1 destruct -X1;
  elim (lift_inv_flat1 … HX2) -HX2 #W2 #U2 #HVW2 #HTU2 #HX2 destruct -X2
  /3 width=5/
| #L #V1 #V2 #W #T1 #T2 #_ #_ #IHV12 #IHT12 #d #e #K #HKL #X1 #HX1 #X2 #HX2
  elim (lift_inv_flat1 … HX1) -HX1 #V0 #X #HV10 #HX #HX1 destruct -X1;
  elim (lift_inv_bind1 … HX) -HX #W0 #T0 #HW0 #HT10 #HX destruct -X;
  elim (lift_inv_bind1 … HX2) -HX2 #V3 #T3 #HV23 #HT23 #HX2 destruct -X2
  /5 width=5/
| #L #K0 #V1 #V2 #V0 #i #HLK0 #HV12 #HV20 #IHV12 #d #e #K #HKL #X #HX #V3 #HV03
  lapply (lift_inv_lref1 … HX) -HX * * #Hid #H destruct -X;
  [ -HV12;
    elim (lift_trans_ge … HV20 … HV03 ?) -HV20 HV03 V0 // #V0 #HV20 #HV03
    elim (drop_trans_le … HKL … HLK0 ?) -HKL HLK0 L /2/ #L #HKL #HLK0
    elim (drop_inv_skip2 … HLK0 ?) -HLK0 /2/ #K1 #V #HK10 #HV #H destruct -L;
    @pr_delta [4,6: // |1,2,3: skip |5: /2 width=5/] (**) (* /2 width=5/ *)
  | -IHV12;
    lapply (lift_trans_be … HV20 … HV03 ? ?) -HV20 HV03 V0 /2/ #HV23
    lapply (drop_trans_ge … HKL … HLK0 ?) -HKL HLK0 L // -Hid #HKK0
    @pr_delta /width=6/
  ]
| #L #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #HV2 #_ #_ #IHV12 #IHW12 #IHT12 #d #e #K #HKL #X1 #HX1 #X2 #HX2
  elim (lift_inv_flat1 … HX1) -HX1 #V0 #X #HV10 #HX #HX1 destruct -X1;
  elim (lift_inv_bind1 … HX) -HX #W0 #T0 #HW0 #HT10 #HX destruct -X;
  elim (lift_inv_bind1 … HX2) -HX2 #W3 #X #HW23 #HX #HX2 destruct -X2;
  elim (lift_inv_flat1 … HX) -HX #V3 #T3 #HV3 #HT23 #HX destruct -X;
  lapply (lift_trans_ge … HV2 … HV3 ?) -HV2 HV3 V // * #V #HV2 #HV3
  @pr_theta /3 width=5/
| #L #V #T #T1 #T2 #HT1 #_ #IHT12 #d #e #K #HKL #X #HX #T0 #HT20
  elim (lift_inv_bind1 … HX) -HX #V3 #T3 #_ #HT3 #HX destruct -X;
  lapply (lift_trans_ge … HT1 … HT3 ?) -HT1 HT3 T // * #T #HT1 #HT3
  @pr_zeta [2: // |1:skip | /2 width=5/] (**) (* /2 width=5/ *)
| #L #V #T1 #T2 #_ #IHT12 #d #e #K #HKL #X #HX #T #HT2
  elim (lift_inv_flat1 … HX) -HX #V0 #T0 #_ #HT0 #HX destruct -X;
  @pr_tau /2 width=5/
]
qed.
*)
axiom tpr_inv_lift: ∀T1,T2. T1 ⇒ T2 →
                    ∀d,e,U1. ↑[d, e] U1 ≡ T1 →
                    ∃∃U2. ↑[d, e] U2 ≡ T2 & U1 ⇒ U2.
(*
#L #T1 #T2 #H elim H -H L T1 T2
[ #L #k #d #e #K #_ #U1 #HU1
  lapply (lift_inv_sort2 … HU1) -HU1 #H destruct -U1 /2/
| #L #i #d #e #K #_ #U1 #HU1
  lapply (lift_inv_lref2 … HU1) -HU1 * * #Hid #H destruct -U1 /3/
| #L #I #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #d #e #K #HLK #X #HX
  elim (lift_inv_bind2 … HX) -HX #V0 #T0 #HV01 #HT01 #HX destruct -X;
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
    [3: -HV32 HV03 @(drop_skip … HLK) /2/ |2: skip ] (**) (* /3 width=5/ is too slow *)
    -HLK HW01
  /3 width=5/
| #L #K0 #V1 #V2 #V0 #i #HLK0 #HV12 #HV20 #IHV12 #d #e #K #HLK #X #HX
  lapply (lift_inv_lref2 … HX) -HX * * #Hid #HX destruct -X;
  [ -HV12;
    elim (drop_conf_lt … HLK … HLK0 Hid) -HLK HLK0 L #L #V3 #HKL #HK0L #HV31
    elim (IHV12 … HK0L … HV31) -IHV12 HK0L HV31 #V4 #HV42 #HV34
    elim (lift_trans_le … HV42 … HV20 ?) -HV42 HV20 V2 // #V2 #HV42
    >arith5 // -Hid #HV20  
    @(ex2_1_intro … V2) /2 width=6/ (**) (* /3 width=8/ is slow *)
  | -IHV12;
    lapply (drop_conf_ge … HLK … HLK0 Hid) -HLK HLK0 L #HK
    elim (lift_free … HV20 d (i - e + 1) ? ? ?) -HV20 /2/
    >arith3 /2/ -Hid /3 width=8/ (**) (* just /3 width=8/ is a bit slow *)
  ]
| #L #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #HV2 #_ #_ #IHV12 #IHW12 #IHT12 #d #e #K #HLK #X #HX
  elim (lift_inv_flat2 … HX) -HX #V0 #Y #HV01 #HY #HX destruct -X;
  elim (lift_inv_bind2 … HY) -HY #W0 #T0 #HW01 #HT01 #HY destruct -Y;
  elim (IHV12 ? ? ? HLK ? HV01) -IHV12 HV01 #V3 #HV32 #HV03
  elim (IHW12 ? ? ? HLK ? HW01) -IHW12 #W3 #HW32 #HW03
  elim (IHT12 … HT01) -IHT12 HT01
    [3: -HV2 HV32 HV03 HW32 HW03 @(drop_skip … HLK) /2/ |2: skip ] (**) (* /3/ is too slow *)
    -HLK HW01 #T3 #HT32 #HT03
  elim (lift_trans_le … HV32 … HV2 ?) -HV32 HV2 V2 // #V2 #HV32 #HV2
  @(ex2_1_intro … (𝕓{Abbr}W3.𝕗{Appl}V2.T3)) /3/ (**) (* /4/ loops *)
| #L #V #T #T1 #T2 #HT1 #_ #IHT12 #d #e #K #HLK #X #HX
  elim (lift_inv_bind2 … HX) -HX #V0 #T0 #_ #HT0 #H destruct -X;
  elim (lift_div_le … HT1 … HT0 ?) -HT1 HT0 T // #T #HT0 #HT1
  elim (IHT12 … HLK … HT1) -IHT12 HLK HT1 /3 width=5/
| #L #V #T1 #T2 #_ #IHT12 #d #e #K #HLK #X #HX
  elim (lift_inv_flat2 … HX) -HX #V0 #T0 #_ #HT01 #H destruct -X;
  elim (IHT12 … HLK … HT01) -IHT12 HLK HT01 /3/
]
qed.
*)