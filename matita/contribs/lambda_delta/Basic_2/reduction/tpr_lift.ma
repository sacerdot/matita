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

include "Basic-2/substitution/tps_lift.ma".
include "Basic-2/reduction/tpr.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON TERMS *********************************)

(* Relocation properties ****************************************************)

(* Basic-1: was: pr0_lift *)
lemma tpr_lift: ∀T1,T2. T1 ⇒ T2 →
                ∀d,e,U1. ↑[d, e] T1 ≡ U1 → ∀U2. ↑[d, e] T2 ≡ U2 → U1 ⇒ U2.
#T1 #T2 #H elim H -H T1 T2
[ * #i #d #e #U1 #HU1 #U2 #HU2
  lapply (lift_mono … HU1 … HU2) -HU1 #H destruct -U1
  [ lapply (lift_inv_sort1 … HU2) -HU2 #H destruct -U2 //
  | lapply (lift_inv_lref1 … HU2) * * #Hid #H destruct -U2 //
  ]
| #I #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #d #e #X1 #HX1 #X2 #HX2
  elim (lift_inv_flat1 … HX1) -HX1 #W1 #U1 #HVW1 #HTU1 #HX1 destruct -X1;
  elim (lift_inv_flat1 … HX2) -HX2 #W2 #U2 #HVW2 #HTU2 #HX2 destruct -X2 /3/
| #V1 #V2 #W #T1 #T2 #_ #_ #IHV12 #IHT12 #d #e #X1 #HX1 #X2 #HX2
  elim (lift_inv_flat1 … HX1) -HX1 #V0 #X #HV10 #HX #HX1 destruct -X1;
  elim (lift_inv_bind1 … HX) -HX #W0 #T0 #HW0 #HT10 #HX destruct -X;
  elim (lift_inv_bind1 … HX2) -HX2 #V3 #T3 #HV23 #HT23 #HX2 destruct -X2 /3/
| #I #V1 #V2 #T1 #T2 #T0 #HV12 #HT12 #HT2 #IHV12 #IHT12 #d #e #X1 #HX1 #X2 #HX2
  elim (lift_inv_bind1 … HX1) -HX1 #W1 #U1 #HVW1 #HTU1 #HX1 destruct -X1;
  elim (lift_inv_bind1 … HX2) -HX2 #W2 #U0 #HVW2 #HTU0 #HX2 destruct -X2;
  elim (lift_total T2 (d + 1) e) #U2 #HTU2
  @tpr_delta
  [4: @(tps_lift_le … HT2 … HTU2 HTU0 ?) /2/ |1: skip |2: /2/ |3: /2/ ] (**) (*/3. is too slow *)
| #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #HV2 #_ #_ #IHV12 #IHW12 #IHT12 #d #e #X1 #HX1 #X2 #HX2
  elim (lift_inv_flat1 … HX1) -HX1 #V0 #X #HV10 #HX #HX1 destruct -X1;
  elim (lift_inv_bind1 … HX) -HX #W0 #T0 #HW0 #HT10 #HX destruct -X;
  elim (lift_inv_bind1 … HX2) -HX2 #W3 #X #HW23 #HX #HX2 destruct -X2;
  elim (lift_inv_flat1 … HX) -HX #V3 #T3 #HV3 #HT23 #HX destruct -X;
  elim (lift_trans_ge … HV2 … HV3 ?) -HV2 HV3 V // /3/
| #V #T #T1 #T2 #HT1 #_ #IHT12 #d #e #X #HX #T0 #HT20
  elim (lift_inv_bind1 … HX) -HX #V3 #T3 #_ #HT3 #HX destruct -X;
  elim (lift_trans_ge … HT1 … HT3 ?) -HT1 HT3 T // /3 width=6/
| #V #T1 #T2 #_ #IHT12 #d #e #X #HX #T #HT2
  elim (lift_inv_flat1 … HX) -HX #V0 #T0 #_ #HT0 #HX destruct -X /3/
]
qed.

(* Basic-1: was: pr0_gen_lift *)
lemma tpr_inv_lift: ∀T1,T2. T1 ⇒ T2 →
                    ∀d,e,U1. ↑[d, e] U1 ≡ T1 →
                    ∃∃U2. ↑[d, e] U2 ≡ T2 & U1 ⇒ U2.
#T1 #T2 #H elim H -H T1 T2
[ * #i #d #e #U1 #HU1
  [ lapply (lift_inv_sort2 … HU1) -HU1 #H destruct -U1 /2/
  | lapply (lift_inv_lref2 … HU1) -HU1 * * #Hid #H destruct -U1 /3/
  ]
| #I #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #d #e #X #HX
  elim (lift_inv_flat2 … HX) -HX #V0 #T0 #HV01 #HT01 #HX destruct -X;
  elim (IHV12 … HV01) -IHV12 HV01;
  elim (IHT12 … HT01) -IHT12 HT01 /3 width=5/
| #V1 #V2 #W1 #T1 #T2 #_ #_ #IHV12 #IHT12 #d #e #X #HX
  elim (lift_inv_flat2 … HX) -HX #V0 #Y #HV01 #HY #HX destruct -X;
  elim (lift_inv_bind2 … HY) -HY #W0 #T0 #HW01 #HT01 #HY destruct -Y;
  elim (IHV12 … HV01) -IHV12 HV01;
  elim (IHT12 … HT01) -IHT12 HT01 /3 width=5/
| #I #V1 #V2 #T1 #T2 #T0 #_ #_ #HT20 #IHV12 #IHT12 #d #e #X #HX
  elim (lift_inv_bind2 … HX) -HX #W1 #U1 #HWV1 #HUT1 #HX destruct -X;
  elim (IHV12 … HWV1) -IHV12 HWV1 #W2 #HWV2 #HW12
  elim (IHT12 … HUT1) -IHT12 HUT1 #U2 #HUT2 #HU12
  elim (tps_inv_lift1_le … HT20 … HUT2 ?) -HT20 HUT2 // [3: /2 width=5/ |2: skip ] #U0 #HU20 #HUT0
  @ex2_1_intro  [2: /2/ |1: skip |3: /2/ ] (**) (* /3 width=5/ is slow *)
| #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #HV2 #_ #_ #IHV12 #IHW12 #IHT12 #d #e #X #HX
  elim (lift_inv_flat2 … HX) -HX #V0 #Y #HV01 #HY #HX destruct -X;
  elim (lift_inv_bind2 … HY) -HY #W0 #T0 #HW01 #HT01 #HY destruct -Y;
  elim (IHV12 … HV01) -IHV12 HV01 #V3 #HV32 #HV03
  elim (IHW12 … HW01) -IHW12 HW01 #W3 #HW32 #HW03
  elim (IHT12 … HT01) -IHT12 HT01 #T3 #HT32 #HT03
  elim (lift_trans_le … HV32 … HV2 ?) -HV32 HV2 V2 // #V2 #HV32 #HV2
  @ex2_1_intro [2: /3/ |1: skip |3: /2/ ] (**) (* /4 width=5/ is slow *)
| #V #T #T1 #T2 #HT1 #_ #IHT12 #d #e #X #HX
  elim (lift_inv_bind2 … HX) -HX #V0 #T0 #_ #HT0 #H destruct -X;
  elim (lift_div_le … HT1 … HT0 ?) -HT1 HT0 T // #T #HT0 #HT1
  elim (IHT12 … HT1) -IHT12 HT1 /3 width=5/
| #V #T1 #T2 #_ #IHT12 #d #e #X #HX
  elim (lift_inv_flat2 … HX) -HX #V0 #T0 #_ #HT01 #H destruct -X;
  elim (IHT12 … HT01) -IHT12 HT01 /3/
]
qed.

(* Advanced inversion lemmas ************************************************)

fact tpr_inv_abst1_aux: ∀U1,U2. U1 ⇒ U2 → ∀V1,T1. U1 = 𝕔{Abst} V1. T1 →
                        ∃∃V2,T2. V1 ⇒ V2 & T1 ⇒ T2 & U2 = 𝕔{Abst} V2. T2.
#U1 #U2 * -U1 U2
[ #I #V #T #H destruct
| #I #V1 #V2 #T1 #T2 #_ #_ #V #T #H destruct
| #V1 #V2 #W #T1 #T2 #_ #_ #V #T #H destruct
| #I #V1 #V2 #T1 #T2 #T #HV12 #HT12 #HT2 #V0 #T0 #H destruct -I V1 T1;
  <(tps_inv_refl_SO2 … HT2 ? ? ?) -HT2 T /2 width=5/
| #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #V0 #T0 #H destruct
| #V #T #T1 #T2 #_ #_ #V0 #T0 #H destruct
| #V #T1 #T2 #_ #V0 #T0 #H destruct
]
qed.

(* Basic-1: was pr0_gen_abst *)
lemma tpr_inv_abst1: ∀V1,T1,U2. 𝕔{Abst} V1. T1 ⇒ U2 →
                     ∃∃V2,T2. V1 ⇒ V2 & T1 ⇒ T2 & U2 = 𝕔{Abst} V2. T2.
/2/ qed.
