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

include "basic_2/substitution/cpy_lift.ma".

(* CONTEXT-SENSITIVE EXTENDED ORDINARY SUBSTITUTION FOR TERMS ***************)

(* Main properties **********************************************************)

(* Basic_1: was: subst1_confluence_eq *)
theorem cpy_conf_eq: ∀G,L,T0,T1,l1,m1. ⦃G, L⦄ ⊢ T0 ▶[l1, m1] T1 →
                     ∀T2,l2,m2. ⦃G, L⦄ ⊢ T0 ▶[l2, m2] T2 →
                     ∃∃T. ⦃G, L⦄ ⊢ T1 ▶[l2, m2] T & ⦃G, L⦄ ⊢ T2 ▶[l1, m1] T.
#G #L #T0 #T1 #l1 #m1 #H elim H -G -L -T0 -T1 -l1 -m1
[ /2 width=3 by ex2_intro/
| #I1 #G #L #K1 #V1 #T1 #i0 #l1 #m1 #Hl1 #Hlm1 #HLK1 #HVT1 #T2 #l2 #m2 #H
  elim (cpy_inv_lref1 … H) -H
  [ #HX destruct /3 width=7 by cpy_subst, ex2_intro/
  | -Hl1 -Hlm1 * #I2 #K2 #V2 #_ #_ #HLK2 #HVT2
    lapply (drop_mono … HLK1 … HLK2) -HLK1 -HLK2 #H destruct
    >(lift_mono … HVT1 … HVT2) -HVT1 -HVT2 /2 width=3 by ex2_intro/
  ]
| #a #I #G #L #V0 #V1 #T0 #T1 #l1 #m1 #_ #_ #IHV01 #IHT01 #X #l2 #m2 #HX
  elim (cpy_inv_bind1 … HX) -HX #V2 #T2 #HV02 #HT02 #HX destruct
  elim (IHV01 … HV02) -IHV01 -HV02 #V #HV1 #HV2
  elim (IHT01 … HT02) -T0 #T #HT1 #HT2
  lapply (lsuby_cpy_trans … HT1 (L.ⓑ{I}V1) ?) -HT1 /2 width=1 by lsuby_succ/
  lapply (lsuby_cpy_trans … HT2 (L.ⓑ{I}V2) ?) -HT2
  /3 width=5 by cpy_bind, lsuby_succ, ex2_intro/
| #I #G #L #V0 #V1 #T0 #T1 #l1 #m1 #_ #_ #IHV01 #IHT01 #X #l2 #m2 #HX
  elim (cpy_inv_flat1 … HX) -HX #V2 #T2 #HV02 #HT02 #HX destruct
  elim (IHV01 … HV02) -V0
  elim (IHT01 … HT02) -T0 /3 width=5 by cpy_flat, ex2_intro/
]
qed-.

(* Basic_1: was: subst1_confluence_neq *)
theorem cpy_conf_neq: ∀G,L1,T0,T1,l1,m1. ⦃G, L1⦄ ⊢ T0 ▶[l1, m1] T1 →
                      ∀L2,T2,l2,m2. ⦃G, L2⦄ ⊢ T0 ▶[l2, m2] T2 →
                      (l1 + m1 ≤ l2 ∨ l2 + m2 ≤ l1) →
                      ∃∃T. ⦃G, L2⦄ ⊢ T1 ▶[l2, m2] T & ⦃G, L1⦄ ⊢ T2 ▶[l1, m1] T.
#G #L1 #T0 #T1 #l1 #m1 #H elim H -G -L1 -T0 -T1 -l1 -m1
[ /2 width=3 by ex2_intro/
| #I1 #G #L1 #K1 #V1 #T1 #i0 #l1 #m1 #Hl1 #Hlm1 #HLK1 #HVT1 #L2 #T2 #l2 #m2 #H1 #H2
  elim (cpy_inv_lref1 … H1) -H1
  [ #H destruct /3 width=7 by cpy_subst, ex2_intro/
  | -HLK1 -HVT1 * #I2 #K2 #V2 #Hl2 #Hlm2 #_ #_ elim H2 -H2 #Hlml [ -Hl1 -Hlm2 | -Hl2 -Hlm1 ]
    [ elim (ylt_yle_false … Hlm1) -Hlm1 /2 width=3 by yle_trans/
    | elim (ylt_yle_false … Hlm2) -Hlm2 /2 width=3 by yle_trans/
    ]
  ]
| #a #I #G #L1 #V0 #V1 #T0 #T1 #l1 #m1 #_ #_ #IHV01 #IHT01 #L2 #X #l2 #m2 #HX #H
  elim (cpy_inv_bind1 … HX) -HX #V2 #T2 #HV02 #HT02 #HX destruct
  elim (IHV01 … HV02 H) -IHV01 -HV02 #V #HV1 #HV2
  elim (IHT01 … HT02) -T0
  [ -H #T #HT1 #HT2
    lapply (lsuby_cpy_trans … HT1 (L2.ⓑ{I}V1) ?) -HT1 /2 width=1 by lsuby_succ/
    lapply (lsuby_cpy_trans … HT2 (L1.ⓑ{I}V2) ?) -HT2 /3 width=5 by cpy_bind, lsuby_succ, ex2_intro/
  | -HV1 -HV2 elim H -H /3 width=1 by yle_succ, or_introl, or_intror/
  ]
| #I #G #L1 #V0 #V1 #T0 #T1 #l1 #m1 #_ #_ #IHV01 #IHT01 #L2 #X #l2 #m2 #HX #H
  elim (cpy_inv_flat1 … HX) -HX #V2 #T2 #HV02 #HT02 #HX destruct
  elim (IHV01 … HV02 H) -V0
  elim (IHT01 … HT02 H) -T0 -H /3 width=5 by cpy_flat, ex2_intro/
]
qed-.

(* Note: the constant 1 comes from cpy_subst *)
(* Basic_1: was: subst1_trans *)
theorem cpy_trans_ge: ∀G,L,T1,T0,l,m. ⦃G, L⦄ ⊢ T1 ▶[l, m] T0 →
                      ∀T2. ⦃G, L⦄ ⊢ T0 ▶[l, 1] T2 → 1 ≤ m → ⦃G, L⦄ ⊢ T1 ▶[l, m] T2.
#G #L #T1 #T0 #l #m #H elim H -G -L -T1 -T0 -l -m
[ #I #G #L #l #m #T2 #H #Hm
  elim (cpy_inv_atom1 … H) -H
  [ #H destruct //
  | * #J #K #V #i #Hl2i #Hilm2 #HLK #HVT2 #H destruct
    lapply (ylt_yle_trans … (l+m) … Hilm2)
    /2 width=5 by cpy_subst, monotonic_yle_plus_sn/
  ]
| #I #G #L #K #V #V2 #i #l #m #Hli #Hilm #HLK #HVW #T2 #HVT2 #Hm
  lapply (cpy_weak … HVT2 0 (i+1) ? ?) -HVT2 /3 width=1 by yle_plus_dx2_trans, yle_succ/
  >yplus_inj #HVT2 <(cpy_inv_lift1_eq … HVW … HVT2) -HVT2 /2 width=5 by cpy_subst/
| #a #I #G #L #V1 #V0 #T1 #T0 #l #m #_ #_ #IHV10 #IHT10 #X #H #Hm
  elim (cpy_inv_bind1 … H) -H #V2 #T2 #HV02 #HT02 #H destruct
  lapply (lsuby_cpy_trans … HT02 (L.ⓑ{I}V1) ?) -HT02 /2 width=1 by lsuby_succ/ #HT02
  lapply (IHT10 … HT02 Hm) -T0 /3 width=1 by cpy_bind/
| #I #G #L #V1 #V0 #T1 #T0 #l #m #_ #_ #IHV10 #IHT10 #X #H #Hm
  elim (cpy_inv_flat1 … H) -H #V2 #T2 #HV02 #HT02 #H destruct /3 width=1 by cpy_flat/
]
qed-.

theorem cpy_trans_down: ∀G,L,T1,T0,l1,m1. ⦃G, L⦄ ⊢ T1 ▶[l1, m1] T0 →
                        ∀T2,l2,m2. ⦃G, L⦄ ⊢ T0 ▶[l2, m2] T2 → l2 + m2 ≤ l1 →
                        ∃∃T. ⦃G, L⦄ ⊢ T1 ▶[l2, m2] T & ⦃G, L⦄ ⊢ T ▶[l1, m1] T2.
#G #L #T1 #T0 #l1 #m1 #H elim H -G -L -T1 -T0 -l1 -m1
[ /2 width=3 by ex2_intro/
| #I #G #L #K #V #W #i1 #l1 #m1 #Hli1 #Hilm1 #HLK #HVW #T2 #l2 #m2 #HWT2 #Hlm2l1
  lapply (yle_trans … Hlm2l1 … Hli1) -Hlm2l1 #Hlm2i1
  lapply (cpy_weak … HWT2 0 (i1+1) ? ?) -HWT2 /3 width=1 by yle_succ, yle_pred_sn/ -Hlm2i1
  >yplus_inj #HWT2 <(cpy_inv_lift1_eq … HVW … HWT2) -HWT2 /3 width=9 by cpy_subst, ex2_intro/
| #a #I #G #L #V1 #V0 #T1 #T0 #l1 #m1 #_ #_ #IHV10 #IHT10 #X #l2 #m2 #HX #lm2l1
  elim (cpy_inv_bind1 … HX) -HX #V2 #T2 #HV02 #HT02 #HX destruct
  lapply (lsuby_cpy_trans … HT02 (L.ⓑ{I}V1) ?) -HT02 /2 width=1 by lsuby_succ/ #HT02
  elim (IHV10 … HV02) -IHV10 -HV02 // #V
  elim (IHT10 … HT02) -T0 /2 width=1 by yle_succ/ #T #HT1 #HT2
  lapply (lsuby_cpy_trans … HT2 (L.ⓑ{I}V) ?) -HT2 /3 width=6 by cpy_bind, lsuby_succ, ex2_intro/
| #I #G #L #V1 #V0 #T1 #T0 #l1 #m1 #_ #_ #IHV10 #IHT10 #X #l2 #m2 #HX #lm2l1
  elim (cpy_inv_flat1 … HX) -HX #V2 #T2 #HV02 #HT02 #HX destruct
  elim (IHV10 … HV02) -V0 //
  elim (IHT10 … HT02) -T0 /3 width=6 by cpy_flat, ex2_intro/
]
qed-.
