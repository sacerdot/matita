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

include "basic_2/substitution/tps_tps.ma".
include "basic_2/unfold/tpss_lift.ma".

(* PARTIAL UNFOLD ON TERMS **************************************************)

(* Advanced inversion lemmas ************************************************)

lemma tpss_inv_SO2: ∀L,T1,T2,d. L ⊢ T1 ▶* [d, 1] T2 → L ⊢ T1 ▶ [d, 1] T2.
#L #T1 #T2 #d #H @(tpss_ind … H) -T2 //
#T #T2 #_ #HT2 #IHT1
lapply (tps_trans_ge … IHT1 … HT2 ?) //
qed-.

(* Advanced properties ******************************************************)

lemma tpss_strip_eq: ∀L,T0,T1,d1,e1. L ⊢ T0 ▶* [d1, e1] T1 →
                     ∀T2,d2,e2. L ⊢ T0 ▶ [d2, e2] T2 →
                     ∃∃T. L ⊢ T1 ▶ [d2, e2] T & L ⊢ T2 ▶* [d1, e1] T.
/3 width=3/ qed.

lemma tpss_strip_neq: ∀L1,T0,T1,d1,e1. L1 ⊢ T0 ▶* [d1, e1] T1 →
                      ∀L2,T2,d2,e2. L2 ⊢ T0 ▶ [d2, e2] T2 →
                      (d1 + e1 ≤ d2 ∨ d2 + e2 ≤ d1) →
                      ∃∃T. L2 ⊢ T1 ▶ [d2, e2] T & L1 ⊢ T2 ▶* [d1, e1] T.
/3 width=3/ qed.

lemma tpss_strap1_down: ∀L,T1,T0,d1,e1. L ⊢ T1 ▶* [d1, e1] T0 →
                        ∀T2,d2,e2. L ⊢ T0 ▶ [d2, e2] T2 → d2 + e2 ≤ d1 →
                        ∃∃T. L ⊢ T1 ▶ [d2, e2] T & L ⊢ T ▶* [d1, e1] T2.
/3 width=3/ qed.

lemma tpss_strap2_down: ∀L,T1,T0,d1,e1. L ⊢ T1 ▶ [d1, e1] T0 →
                        ∀T2,d2,e2. L ⊢ T0 ▶* [d2, e2] T2 → d2 + e2 ≤ d1 →
                        ∃∃T. L ⊢ T1 ▶* [d2, e2] T & L ⊢ T ▶ [d1, e1] T2.
/3 width=3/ qed.

lemma tpss_split_up: ∀L,T1,T2,d,e. L ⊢ T1 ▶* [d, e] T2 →
                     ∀i. d ≤ i → i ≤ d + e →
                     ∃∃T. L ⊢ T1 ▶* [d, i - d] T & L ⊢ T ▶* [i, d + e - i] T2.
#L #T1 #T2 #d #e #H #i #Hdi #Hide @(tpss_ind … H) -T2
[ /2 width=3/
| #T #T2 #_ #HT12 * #T3 #HT13 #HT3
  elim (tps_split_up … HT12 … Hdi Hide) -HT12 -Hide #T0 #HT0 #HT02
  elim (tpss_strap1_down … HT3 … HT0 ?) -T [2: >commutative_plus /2 width=1/ ]
  /3 width=7 by ex2_intro, step/ (**) (* just /3 width=7/ is too slow *)
]
qed.

lemma tpss_inv_lift1_up: ∀L,U1,U2,dt,et. L ⊢ U1 ▶* [dt, et] U2 →
                         ∀K,d,e. ⇩[d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 →
                         d ≤ dt → dt ≤ d + e → d + e ≤ dt + et →
                         ∃∃T2. K ⊢ T1 ▶* [d, dt + et - (d + e)] T2 &
                               ⇧[d, e] T2 ≡ U2.
#L #U1 #U2 #dt #et #HU12 #K #d #e #HLK #T1 #HTU1 #Hddt #Hdtde #Hdedet
elim (tpss_split_up … HU12 (d + e) ? ?) -HU12 // -Hdedet #U #HU1 #HU2
lapply (tpss_weak … HU1 d e ? ?) -HU1 // [ >commutative_plus /2 width=1/ ] -Hddt -Hdtde #HU1
lapply (tpss_inv_lift1_eq … HU1 … HTU1) -HU1 #HU1 destruct
elim (tpss_inv_lift1_ge … HU2 … HLK … HTU1 ?) -HU2 -HLK -HTU1 // <minus_plus_m_m /2 width=3/
qed.

(* Main properties **********************************************************)

theorem tpss_conf_eq: ∀L,T0,T1,d1,e1. L ⊢ T0 ▶* [d1, e1] T1 →
                      ∀T2,d2,e2. L ⊢ T0 ▶* [d2, e2] T2 →
                      ∃∃T. L ⊢ T1 ▶* [d2, e2] T & L ⊢ T2 ▶* [d1, e1] T.
/3 width=3/ qed.

theorem tpss_conf_neq: ∀L1,T0,T1,d1,e1. L1 ⊢ T0 ▶* [d1, e1] T1 →
                       ∀L2,T2,d2,e2. L2 ⊢ T0 ▶* [d2, e2] T2 →
                       (d1 + e1 ≤ d2 ∨ d2 + e2 ≤ d1) →
                       ∃∃T. L2 ⊢ T1 ▶* [d2, e2] T & L1 ⊢ T2 ▶* [d1, e1] T.
/3 width=3/ qed.

theorem tpss_trans_eq: ∀L,T1,T,T2,d,e.
                       L ⊢ T1 ▶* [d, e] T → L ⊢ T ▶* [d, e] T2 →
                       L ⊢ T1 ▶* [d, e] T2.
/2 width=3/ qed.

theorem tpss_trans_down: ∀L,T1,T0,d1,e1. L ⊢ T1 ▶* [d1, e1] T0 →
                         ∀T2,d2,e2. L ⊢ T0 ▶* [d2, e2] T2 → d2 + e2 ≤ d1 →
                         ∃∃T. L ⊢ T1 ▶* [d2, e2] T & L ⊢ T ▶* [d1, e1] T2.
/3 width=3/ qed.
