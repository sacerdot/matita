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

include "basic_2/substitution/tps_lift.ma".
include "basic_2/reducibility/tpr.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON TERMS *********************************)

(* Relocation properties ****************************************************)

(* Basic_1: was: pr0_lift *)
lemma tpr_lift: t_liftable tpr.
#T1 #T2 #H elim H -T1 -T2
[ * #i #U1 #d #e #HU1 #U2 #HU2
  lapply (lift_mono … HU1 … HU2) -HU1 #H destruct
  [ lapply (lift_inv_sort1 … HU2) -HU2 #H destruct //
  | lapply (lift_inv_lref1 … HU2) * * #Hid #H destruct //
  | lapply (lift_inv_gref1 … HU2) -HU2 #H destruct //
  ]
| #I #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #X1 #d #e #HX1 #X2 #HX2
  elim (lift_inv_flat1 … HX1) -HX1 #W1 #U1 #HVW1 #HTU1 #HX1 destruct
  elim (lift_inv_flat1 … HX2) -HX2 #W2 #U2 #HVW2 #HTU2 #HX2 destruct /3 width=4/
| #a #V1 #V2 #W #T1 #T2 #_ #_ #IHV12 #IHT12 #X1 #d #e #HX1 #X2 #HX2
  elim (lift_inv_flat1 … HX1) -HX1 #V0 #X #HV10 #HX #HX1 destruct
  elim (lift_inv_bind1 … HX) -HX #W0 #T0 #HW0 #HT10 #HX destruct
  elim (lift_inv_bind1 … HX2) -HX2 #V3 #T3 #HV23 #HT23 #HX2 destruct /3 width=4/
| #a #I #V1 #V2 #T1 #T #T2 #_ #_ #HT2 #IHV12 #IHT1 #X1 #d #e #HX1 #X2 #HX2
  elim (lift_inv_bind1 … HX1) -HX1 #W1 #U1 #HVW1 #HTU1 #HX1 destruct
  elim (lift_inv_bind1 … HX2) -HX2 #W2 #U0 #HVW2 #HTU0 #HX2 destruct
  elim (lift_total T (d + 1) e) #U #HTU
  @tpr_delta
  [4: @(tps_lift_le … HT2 … HTU HTU0 ?) /2 width=1/ |1: skip |2: /2 width=4/ |3: /2 width=4/ ] (**) (*/3. is too slow *)
| #a #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #HV2 #_ #_ #IHV12 #IHW12 #IHT12 #X1 #d #e #HX1 #X2 #HX2
  elim (lift_inv_flat1 … HX1) -HX1 #V0 #X #HV10 #HX #HX1 destruct
  elim (lift_inv_bind1 … HX) -HX #W0 #T0 #HW0 #HT10 #HX destruct
  elim (lift_inv_bind1 … HX2) -HX2 #W3 #X #HW23 #HX #HX2 destruct
  elim (lift_inv_flat1 … HX) -HX #V3 #T3 #HV3 #HT23 #HX destruct
  elim (lift_trans_ge … HV2 … HV3 ?) -V // /3 width=4/
| #V #T1 #T #T2 #_ #HT2 #IHT1 #X #d #e #H #U2 #HTU2
  elim (lift_inv_bind1 … H) -H #V3 #T3 #_ #HT13 #H destruct -V
  elim (lift_conf_O1 … HTU2 … HT2) -T2 /3 width=4/
| #V #T1 #T2 #_ #IHT12 #X #d #e #HX #T #HT2
  elim (lift_inv_flat1 … HX) -HX #V0 #T0 #_ #HT0 #HX destruct /3 width=4/
]
qed.

(* Basic_1: was: pr0_gen_lift *)
lemma tpr_inv_lift1: t_deliftable_sn tpr.
#T1 #T2 #H elim H -T1 -T2
[ * #i #X #d #e #HX
  [ lapply (lift_inv_sort2 … HX) -HX #H destruct /2 width=3/
  | lapply (lift_inv_lref2 … HX) -HX * * #Hid #H destruct /3 width=3/
  | lapply (lift_inv_gref2 … HX) -HX #H destruct /2 width=3/
  ]
| #I #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #X #d #e #HX
  elim (lift_inv_flat2 … HX) -HX #V0 #T0 #HV01 #HT01 #HX destruct
  elim (IHV12 … HV01) -V1
  elim (IHT12 … HT01) -T1 /3 width=5/
| #a #V1 #V2 #W1 #T1 #T2 #_ #_ #IHV12 #IHT12 #X #d #e #HX
  elim (lift_inv_flat2 … HX) -HX #V0 #Y #HV01 #HY #HX destruct
  elim (lift_inv_bind2 … HY) -HY #W0 #T0 #HW01 #HT01 #HY destruct
  elim (IHV12 … HV01) -V1
  elim (IHT12 … HT01) -T1 /3 width=5/
| #a #I #V1 #V2 #T1 #T #T2 #_ #_ #HT2 #IHV12 #IHT1 #X #d #e #HX
  elim (lift_inv_bind2 … HX) -HX #W1 #U1 #HWV1 #HUT1 #HX destruct
  elim (IHV12 … HWV1) -V1 #W2 #HWV2 #HW12
  elim (IHT1 … HUT1) -T1 #U #HUT #HU1
  elim (tps_inv_lift1_le … HT2 … HUT ?) -T // [3: /2 width=5/ |2: skip ] #U2 #HU2 #HUT2
  @ex2_intro  [2: /2 width=2/ |1: skip |3: /2 width=3/ ] (**) (* /3 width=5/ is slow *)
| #a #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #HV2 #_ #_ #IHV12 #IHW12 #IHT12 #X #d #e #HX
  elim (lift_inv_flat2 … HX) -HX #V0 #Y #HV01 #HY #HX destruct
  elim (lift_inv_bind2 … HY) -HY #W0 #T0 #HW01 #HT01 #HY destruct
  elim (IHV12 … HV01) -V1 #V3 #HV32 #HV03
  elim (IHW12 … HW01) -W1 #W3 #HW32 #HW03
  elim (IHT12 … HT01) -T1 #T3 #HT32 #HT03
  elim (lift_trans_le … HV32 … HV2 ?) -V2 // #V2 #HV32 #HV2
  @ex2_intro [2: /3 width=2/ |1: skip |3: /2 width=3/ ] (**) (* /4 width=5/ is slow *)
| #V #T1 #T #T2 #_ #HT2 #IHT1 #X #d #e #HX
  elim (lift_inv_bind2 … HX) -HX #V3 #T3 #_ #HT31 #H destruct
  elim (IHT1 … HT31) -T1 #T1 #HT1 #HT31
  elim (lift_div_le … HT2 … HT1 ?) -T // /3 width=5/
| #V #T1 #T2 #_ #IHT12 #X #d #e #HX
  elim (lift_inv_flat2 … HX) -HX #V0 #T0 #_ #HT01 #H destruct
  elim (IHT12 … HT01) -T1 /3 width=3/
]
qed-.

(* Advanced inversion lemmas ************************************************)

(* Basic_1: was pr0_gen_abst *)
lemma tpr_inv_abst1: ∀a,V1,T1,U2. ⓛ{a}V1. T1 ➡ U2 →
                     ∃∃V2,T2. V1 ➡ V2 & T1 ➡ T2 & U2 = ⓛ{a}V2. T2.
#a #V1 #T1 #U2 #H elim (tpr_inv_bind1 … H) -H *
[ #V2 #T #T2 #HV12 #HT1 #HT2
  lapply (tps_inv_refl_SO2 … HT2 ???) -HT2 // /2 width=5/
| #T2 #_ #_ #_ #H destruct
]
qed-.

(* Advanced forward lemmas **************************************************)

lemma tpr_fwd_abst1: ∀a,V1,T1,U2. ⓛ{a}V1.T1 ➡ U2 → ∀b,I,W.
                     ∃∃V2,T2. ⓑ{b,I}W.T1 ➡ ⓑ{b,I}W.T2 &
                              U2 = ⓛ{a}V2.T2.
#a #V1 #T1 #U2 #H #b #I #W elim (tpr_inv_bind1 … H) -H *
[ #V2 #T #T2 #HV12 #HT1 #HT2
  lapply (tps_inv_refl_SO2 … HT2 ???) -HT2 // /3 width=4/
| #T2 #_ #_ #_ #H destruct
]
qed-.
