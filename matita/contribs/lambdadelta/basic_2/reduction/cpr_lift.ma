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

include "basic_2/relocation/ldrop_ldrop.ma".
include "basic_2/reduction/cpr.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION FOR TERMS ***************************)

(* Relocation properties ****************************************************)

(* Basic_1: includes: pr0_lift pr2_lift *)
lemma cpr_lift: l_liftable cpr.
#K #T1 #T2 #H elim H -K -T1 -T2
[ #I #K #L #d #e #_ #U1 #H1 #U2 #H2
  >(lift_mono … H1 … H2) -H1 -H2 //
| #K #KV #V #V2 #W2 #i #HKV #HV2 #HVW2 #IHV2 #L #d #e #HLK #U1 #H #U2 #HWU2
  elim (lift_inv_lref1 … H) * #Hid #H destruct
  [ elim (lift_trans_ge … HVW2 … HWU2) -W2 // <minus_plus #W2 #HVW2 #HWU2
    elim (ldrop_trans_le … HLK … HKV) -K /2 width=2/ #X #HLK #H
    elim (ldrop_inv_skip2 … H) -H /2 width=1/ -Hid #K #Y #HKV #HVY #H destruct /3 width=8/
  | lapply (lift_trans_be … HVW2 … HWU2 ? ?) -W2 // /2 width=1/ >plus_plus_comm_23 #HVU2
    lapply (ldrop_trans_ge_comm … HLK … HKV ?) -K // -Hid /3 width=6/
  ]
| #a #I #K #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #L #d #e #HLK #U1 #H1 #U2 #H2
  elim (lift_inv_bind1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1 destruct
  elim (lift_inv_bind1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct /4 width=5/
| #I #K #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #L #d #e #HLK #U1 #H1 #U2 #H2
  elim (lift_inv_flat1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1 destruct
  elim (lift_inv_flat1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct /3 width=6/
| #K #V #T1 #T #T2 #_ #HT2 #IHT1 #L #d #e #HLK #U1 #H #U2 #HTU2
  elim (lift_inv_bind1 … H) -H #VV1 #TT1 #HVV1 #HTT1 #H destruct
  elim (lift_conf_O1 … HTU2 … HT2) -T2 /4 width=5/
| #K #V #T1 #T2 #_ #IHT12 #L #d #e #HLK #U1 #H #U2 #HTU2
  elim (lift_inv_flat1 … H) -H #VV1 #TT1 #HVV1 #HTT1 #H destruct /3 width=5/
| #a #K #V1 #V2 #W #T1 #T2 #_ #_ #IHV12 #IHT12 #L #d #e #HLK #X1 #HX1 #X2 #HX2
  elim (lift_inv_flat1 … HX1) -HX1 #V0 #X #HV10 #HX #HX1 destruct
  elim (lift_inv_bind1 … HX) -HX #W0 #T0 #HW0 #HT10 #HX destruct
  elim (lift_inv_bind1 … HX2) -HX2 #V3 #T3 #HV23 #HT23 #HX2 destruct /4 width=5/
| #a #K #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #HV2 #_ #_ #IHV1 #IHW12 #IHT12 #L #d #e #HLK #X1 #HX1 #X2 #HX2
  elim (lift_inv_flat1 … HX1) -HX1 #V0 #X #HV10 #HX #HX1 destruct
  elim (lift_inv_bind1 … HX) -HX #W0 #T0 #HW0 #HT10 #HX destruct
  elim (lift_inv_bind1 … HX2) -HX2 #W3 #X #HW23 #HX #HX2 destruct
  elim (lift_inv_flat1 … HX) -HX #V3 #T3 #HV3 #HT23 #HX destruct
  elim (lift_trans_ge … HV2 … HV3 ?) -V2 // /4 width=5/
]
qed.

(* Basic_1: includes: pr0_gen_lift pr2_gen_lift *)
lemma cpr_inv_lift1: l_deliftable_sn cpr.
#L #U1 #U2 #H elim H -L -U1 -U2
[ * #L #i #K #d #e #_ #T1 #H
  [ lapply (lift_inv_sort2 … H) -H #H destruct /2 width=3/
  | elim (lift_inv_lref2 … H) -H * #Hid #H destruct /3 width=3/
  | lapply (lift_inv_gref2 … H) -H #H destruct /2 width=3/
  ]
| #L #LV #V #V2 #W2 #i #HLV #HV2 #HVW2 #IHV2 #K #d #e #HLK #T1 #H
  elim (lift_inv_lref2 … H) -H * #Hid #H destruct
  [ elim (ldrop_conf_lt … HLK … HLV) -L // #L #U #HKL #HLV #HUV
    elim (IHV2 … HLV … HUV) -V #U2 #HUV2 #HU2
    elim (lift_trans_le … HUV2 … HVW2) -V2 // >minus_plus <plus_minus_m_m // -Hid /3 width=8/
  | elim (le_inv_plus_l … Hid) #Hdie #Hei
    lapply (ldrop_conf_ge … HLK … HLV ?) -L // #HKLV
    elim (lift_split … HVW2 d (i - e + 1)) -HVW2 [4: // |3: /2 width=1/ |2: /3 width=1/ ] -Hid -Hdie
    #V1 #HV1 >plus_minus // <minus_minus // /2 width=1/ <minus_n_n <plus_n_O /3 width=8/
  ]
| #a #I #L #V1 #V2 #U1 #U2 #_ #_ #IHV12 #IHU12 #K #d #e #HLK #X #H
  elim (lift_inv_bind2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct
  elim (IHV12 … HLK … HWV1) -IHV12 #W2 #HW12 #HWV2
  elim (IHU12 … HTU1) -IHU12 -HTU1 /3 width=5/
| #I #L #V1 #V2 #U1 #U2 #_ #_ #IHV12 #IHU12 #K #d #e #HLK #X #H
  elim (lift_inv_flat2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct
  elim (IHV12 … HLK … HWV1) -V1
  elim (IHU12 … HLK … HTU1) -U1 -HLK /3 width=5/
| #L #V #U1 #U #U2 #_ #HU2 #IHU1 #K #d #e #HLK #X #H
  elim (lift_inv_bind2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct
  elim (IHU1 (K.ⓓW1) … HTU1) /2 width=1/ -L -U1 #T #HTU #HT1
  elim (lift_div_le … HU2 … HTU) -U // /3 width=5/
| #L #V #U1 #U2 #_ #IHU12 #K #d #e #HLK #X #H
  elim (lift_inv_flat2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct
  elim (IHU12 … HLK … HTU1) -L -U1 /3 width=3/
| #a #L #V1 #V2 #W #T1 #T2 #_ #_ #IHV12 #IHT12 #K #d #e #HLK #X #HX
  elim (lift_inv_flat2 … HX) -HX #V0 #Y #HV01 #HY #HX destruct
  elim (lift_inv_bind2 … HY) -HY #W0 #T0 #HW01 #HT01 #HY destruct
  elim (IHV12 … HLK … HV01) -V1
  elim (IHT12 (K.ⓛW0) … HT01) -T1 /2 width=1/ /3 width=5/
| #a #L #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #HV2 #_ #_ #IHV1 #IHW12 #IHT12 #K #d #e #HLK #X #HX
  elim (lift_inv_flat2 … HX) -HX #V0 #Y #HV01 #HY #HX destruct
  elim (lift_inv_bind2 … HY) -HY #W0 #T0 #HW01 #HT01 #HY destruct
  elim (IHV1 … HLK … HV01) -V1 #V3 #HV3 #HV03
  elim (IHT12 (K.ⓓW0) … HT01) -T1 /2 width=1/ #T3 #HT32 #HT03
  elim (IHW12 … HLK … HW01) -W1 #W3 #HW32 #HW03
  elim (lift_trans_le … HV3 … HV2 ?) -V // #V #HV3 #HV2
  @ex2_intro [2: /3 width=2/ | skip |3: /2 width=3/ ] (**) (* /4 width=5/ is slow *)
]
qed-.