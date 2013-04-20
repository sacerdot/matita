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
include "basic_2/substitution/cpss.ma".

(* CONTEXT-SENSITIVE PARALLEL SUBSTITUTION FOR TERMS ************************)

(* Relocation properties ****************************************************)

(* Basic_1: was only: subst1_lift_lt subst1_lift_ge *)
lemma cpss_lift: l_liftable cpss.
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
]
qed.

(* Basic_1: was only: subst1_gen_lift_lt subst1_gen_lift_ge *)
lemma cpss_inv_lift1: l_deliftable_sn cpss.
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
]
qed-.
