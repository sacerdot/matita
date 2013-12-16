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

(* PARALLEL SUBSTITUTION ON TERMS *******************************************)

(* Main properties **********************************************************)

(* Basic_1: was: subst1_confluence_eq *)
theorem tps_conf_eq: ∀L,T0,T1,d1,e1. L ⊢ T0 ▶ [d1, e1] T1 →
                     ∀T2,d2,e2. L ⊢ T0 ▶ [d2, e2] T2 →
                     ∃∃T. L ⊢ T1 ▶ [d2, e2] T & L ⊢ T2 ▶ [d1, e1] T.
#L #T0 #T1 #d1 #e1 #H elim H -L -T0 -T1 -d1 -e1
[ /2 width=3/
| #L #K1 #V1 #T1 #i0 #d1 #e1 #Hd1 #Hde1 #HLK1 #HVT1 #T2 #d2 #e2 #H
  elim (tps_inv_lref1 … H) -H
  [ #HX destruct /3 width=6/
  | -Hd1 -Hde1 * #K2 #V2 #_ #_ #HLK2 #HVT2
    lapply (ldrop_mono … HLK1 … HLK2) -HLK1 -HLK2 #H destruct
    >(lift_mono … HVT1 … HVT2) -HVT1 -HVT2 /2 width=3/
  ]
| #L #a #I #V0 #V1 #T0 #T1 #d1 #e1 #_ #_ #IHV01 #IHT01 #X #d2 #e2 #HX
  elim (tps_inv_bind1 … HX) -HX #V2 #T2 #HV02 #HT02 #HX destruct
  lapply (tps_lsubr_trans … HT02 (L. ⓑ{I} V1) ?) -HT02 /2 width=1/ #HT02
  elim (IHV01 … HV02) -V0 #V #HV1 #HV2
  elim (IHT01 … HT02) -T0 #T #HT1 #HT2
  lapply (tps_lsubr_trans … HT1 (L. ⓑ{I} V) ?) -HT1 /2 width=1/
  lapply (tps_lsubr_trans … HT2 (L. ⓑ{I} V) ?) -HT2 /3 width=5/
| #L #I #V0 #V1 #T0 #T1 #d1 #e1 #_ #_ #IHV01 #IHT01 #X #d2 #e2 #HX
  elim (tps_inv_flat1 … HX) -HX #V2 #T2 #HV02 #HT02 #HX destruct
  elim (IHV01 … HV02) -V0
  elim (IHT01 … HT02) -T0 /3 width=5/
]
qed.

(* Basic_1: was: subst1_confluence_neq *)
theorem tps_conf_neq: ∀L1,T0,T1,d1,e1. L1 ⊢ T0 ▶ [d1, e1] T1 →
                      ∀L2,T2,d2,e2. L2 ⊢ T0 ▶ [d2, e2] T2 →
                      (d1 + e1 ≤ d2 ∨ d2 + e2 ≤ d1) →
                      ∃∃T. L2 ⊢ T1 ▶ [d2, e2] T & L1 ⊢ T2 ▶ [d1, e1] T.
#L1 #T0 #T1 #d1 #e1 #H elim H -L1 -T0 -T1 -d1 -e1
[ /2 width=3/
| #L1 #K1 #V1 #T1 #i0 #d1 #e1 #Hd1 #Hde1 #HLK1 #HVT1 #L2 #T2 #d2 #e2 #H1 #H2
  elim (tps_inv_lref1 … H1) -H1
  [ #H destruct /3 width=6/
  | -HLK1 -HVT1 * #K2 #V2 #Hd2 #Hde2 #_ #_ elim H2 -H2 #Hded
    [ -Hd1 -Hde2
      lapply (transitive_le … Hded Hd2) -Hded -Hd2 #H
      lapply (lt_to_le_to_lt … Hde1 H) -Hde1 -H #H
      elim (lt_refl_false … H)
    | -Hd2 -Hde1
      lapply (transitive_le … Hded Hd1) -Hded -Hd1 #H
      lapply (lt_to_le_to_lt … Hde2 H) -Hde2 -H #H
      elim (lt_refl_false … H)
    ]
  ]
| #L1 #a #I #V0 #V1 #T0 #T1 #d1 #e1 #_ #_ #IHV01 #IHT01 #L2 #X #d2 #e2 #HX #H
  elim (tps_inv_bind1 … HX) -HX #V2 #T2 #HV02 #HT02 #HX destruct
  elim (IHV01 … HV02 H) -V0 #V #HV1 #HV2
  elim (IHT01 … HT02 ?) -T0
  [ -H #T #HT1 #HT2
    lapply (tps_lsubr_trans … HT1 (L2. ⓑ{I} V) ?) -HT1 /2 width=1/
    lapply (tps_lsubr_trans … HT2 (L1. ⓑ{I} V) ?) -HT2 /2 width=1/ /3 width=5/
  | -HV1 -HV2 >plus_plus_comm_23 >plus_plus_comm_23 in ⊢ (? ? %); elim H -H #H
    [ @or_introl | @or_intror ] /2 by monotonic_le_plus_l/ (**) (* /3 / is too slow *)
  ]
| #L1 #I #V0 #V1 #T0 #T1 #d1 #e1 #_ #_ #IHV01 #IHT01 #L2 #X #d2 #e2 #HX #H
  elim (tps_inv_flat1 … HX) -HX #V2 #T2 #HV02 #HT02 #HX destruct
  elim (IHV01 … HV02 H) -V0
  elim (IHT01 … HT02 H) -T0 -H /3 width=5/
]
qed.

(* Note: the constant 1 comes from tps_subst *)
(* Basic_1: was: subst1_trans *)
theorem tps_trans_ge: ∀L,T1,T0,d,e. L ⊢ T1 ▶ [d, e] T0 →
                      ∀T2. L ⊢ T0 ▶ [d, 1] T2 → 1 ≤ e →
                      L ⊢ T1 ▶ [d, e] T2.
#L #T1 #T0 #d #e #H elim H -L -T1 -T0 -d -e
[ #L #I #d #e #T2 #H #He
  elim (tps_inv_atom1 … H) -H
  [ #H destruct //
  | * #K #V #i #Hd2i #Hide2 #HLK #HVT2 #H destruct
    lapply (lt_to_le_to_lt … (d + e) Hide2 ?) /2 width=4/
  ]
| #L #K #V #V2 #i #d #e #Hdi #Hide #HLK #HVW #T2 #HVT2 #He
  lapply (tps_weak … HVT2 0 (i +1) ? ?) -HVT2 /2 width=1/ #HVT2
  <(tps_inv_lift1_eq … HVT2 … HVW) -HVT2 /2 width=4/
| #L #a #I #V1 #V0 #T1 #T0 #d #e #_ #_ #IHV10 #IHT10 #X #H #He
  elim (tps_inv_bind1 … H) -H #V2 #T2 #HV02 #HT02 #H destruct
  lapply (tps_lsubr_trans … HT02 (L. ⓑ{I} V0) ?) -HT02 /2 width=1/ #HT02
  lapply (IHT10 … HT02 He) -T0 #HT12
  lapply (tps_lsubr_trans … HT12 (L. ⓑ{I} V2) ?) -HT12 /2 width=1/ /3 width=1/
| #L #I #V1 #V0 #T1 #T0 #d #e #_ #_ #IHV10 #IHT10 #X #H #He
  elim (tps_inv_flat1 … H) -H #V2 #T2 #HV02 #HT02 #H destruct /3 width=1/
]
qed.

theorem tps_trans_down: ∀L,T1,T0,d1,e1. L ⊢ T1 ▶ [d1, e1] T0 →
                        ∀T2,d2,e2. L ⊢ T0 ▶ [d2, e2] T2 → d2 + e2 ≤ d1 →
                        ∃∃T. L ⊢ T1 ▶ [d2, e2] T & L ⊢ T ▶ [d1, e1] T2.
#L #T1 #T0 #d1 #e1 #H elim H -L -T1 -T0 -d1 -e1
[ /2 width=3/
| #L #K #V #W #i1 #d1 #e1 #Hdi1 #Hide1 #HLK #HVW #T2 #d2 #e2 #HWT2 #Hde2d1
  lapply (transitive_le … Hde2d1 Hdi1) -Hde2d1 #Hde2i1
  lapply (tps_weak … HWT2 0 (i1 + 1) ? ?) -HWT2 normalize /2 width=1/ -Hde2i1 #HWT2
  <(tps_inv_lift1_eq … HWT2 … HVW) -HWT2 /3 width=8/
| #L #a #I #V1 #V0 #T1 #T0 #d1 #e1 #_ #_ #IHV10 #IHT10 #X #d2 #e2 #HX #de2d1
  elim (tps_inv_bind1 … HX) -HX #V2 #T2 #HV02 #HT02 #HX destruct
  lapply (tps_lsubr_trans … HT02 (L. ⓑ{I} V0) ?) -HT02 /2 width=1/ #HT02
  elim (IHV10 … HV02 ?) -IHV10 -HV02 // #V
  elim (IHT10 … HT02 ?) -T0 /2 width=1/ #T #HT1 #HT2
  lapply (tps_lsubr_trans … HT1 (L. ⓑ{I} V) ?) -HT1 /2 width=1/
  lapply (tps_lsubr_trans … HT2 (L. ⓑ{I} V2) ?) -HT2 /2 width=1/ /3 width=6/
| #L #I #V1 #V0 #T1 #T0 #d1 #e1 #_ #_ #IHV10 #IHT10 #X #d2 #e2 #HX #de2d1
  elim (tps_inv_flat1 … HX) -HX #V2 #T2 #HV02 #HT02 #HX destruct
  elim (IHV10 … HV02 ?) -V0 //
  elim (IHT10 … HT02 ?) -T0 // /3 width=6/
]
qed.
