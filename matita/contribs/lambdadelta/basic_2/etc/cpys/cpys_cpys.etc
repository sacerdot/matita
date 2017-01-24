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

include "basic_2/substitution/cpy_cpy.ma".
include "basic_2/multiple/cpys_alt.ma".

(* CONTEXT-SENSITIVE EXTENDED MULTIPLE SUBSTITUTION FOR TERMS ***************)

(* Advanced inversion lemmas ************************************************)

lemma cpys_inv_SO2: ∀G,L,T1,T2,l. ⦃G, L⦄ ⊢ T1 ▶*[l, 1] T2 → ⦃G, L⦄ ⊢ T1 ▶[l, 1] T2.
#G #L #T1 #T2 #l #H @(cpys_ind … H) -T2 /2 width=3 by cpy_trans_ge/
qed-.

(* Advanced properties ******************************************************)

lemma cpys_strip_eq: ∀G,L,T0,T1,l1,m1. ⦃G, L⦄ ⊢ T0 ▶*[l1, m1] T1 →
                     ∀T2,l2,m2. ⦃G, L⦄ ⊢ T0 ▶[l2, m2] T2 →
                     ∃∃T. ⦃G, L⦄ ⊢ T1 ▶[l2, m2] T & ⦃G, L⦄ ⊢ T2 ▶*[l1, m1] T.
normalize /3 width=3 by cpy_conf_eq, TC_strip1/ qed-.

lemma cpys_strip_neq: ∀G,L1,T0,T1,l1,m1. ⦃G, L1⦄ ⊢ T0 ▶*[l1, m1] T1 →
                      ∀L2,T2,l2,m2. ⦃G, L2⦄ ⊢ T0 ▶[l2, m2] T2 →
                      (l1 + m1 ≤ l2 ∨ l2 + m2 ≤ l1) →
                      ∃∃T. ⦃G, L2⦄ ⊢ T1 ▶[l2, m2] T & ⦃G, L1⦄ ⊢ T2 ▶*[l1, m1] T.
normalize /3 width=3 by cpy_conf_neq, TC_strip1/ qed-.

lemma cpys_strap1_down: ∀G,L,T1,T0,l1,m1. ⦃G, L⦄ ⊢ T1 ▶*[l1, m1] T0 →
                        ∀T2,l2,m2. ⦃G, L⦄ ⊢ T0 ▶[l2, m2] T2 → l2 + m2 ≤ l1 →
                        ∃∃T. ⦃G, L⦄ ⊢ T1 ▶[l2, m2] T & ⦃G, L⦄ ⊢ T ▶*[l1, m1] T2.
normalize /3 width=3 by cpy_trans_down, TC_strap1/ qed.

lemma cpys_strap2_down: ∀G,L,T1,T0,l1,m1. ⦃G, L⦄ ⊢ T1 ▶[l1, m1] T0 →
                        ∀T2,l2,m2. ⦃G, L⦄ ⊢ T0 ▶*[l2, m2] T2 → l2 + m2 ≤ l1 →
                        ∃∃T. ⦃G, L⦄ ⊢ T1 ▶*[l2, m2] T & ⦃G, L⦄ ⊢ T ▶[l1, m1] T2.
normalize /3 width=3 by cpy_trans_down, TC_strap2/ qed-.

lemma cpys_split_up: ∀G,L,T1,T2,l,m. ⦃G, L⦄ ⊢ T1 ▶*[l, m] T2 →
                     ∀i. l ≤ i → i ≤ l + m →
                     ∃∃T. ⦃G, L⦄ ⊢ T1 ▶*[l, i - l] T & ⦃G, L⦄ ⊢ T ▶*[i, l + m - i] T2.
#G #L #T1 #T2 #l #m #H #i #Hli #Hilm @(cpys_ind … H) -T2
[ /2 width=3 by ex2_intro/
| #T #T2 #_ #HT12 * #T3 #HT13 #HT3
  elim (cpy_split_up … HT12 … Hilm) -HT12 -Hilm #T0 #HT0 #HT02
  elim (cpys_strap1_down … HT3 … HT0) -T /3 width=5 by cpys_strap1, ex2_intro/
  >ymax_pre_sn_comm //
]
qed-.

lemma cpys_inv_lift1_up: ∀G,L,U1,U2,lt,mt. ⦃G, L⦄ ⊢ U1 ▶*[lt, mt] U2 →
                         ∀K,s,l,m. ⬇[s, l, m] L ≡ K → ∀T1. ⬆[l, m] T1 ≡ U1 →
                         l ≤ lt → lt ≤ l + m → l + m ≤ lt + mt →
                         ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶*[l, lt + mt - (l + m)] T2 &
                               ⬆[l, m] T2 ≡ U2.
#G #L #U1 #U2 #lt #mt #HU12 #K #s #l #m #HLK #T1 #HTU1 #Hllt #Hltlm #Hlmlmt
elim (cpys_split_up … HU12 (l + m)) -HU12 // -Hlmlmt #U #HU1 #HU2
lapply (cpys_weak … HU1 l m ? ?) -HU1 // [ >ymax_pre_sn_comm // ] -Hllt -Hltlm #HU1
lapply (cpys_inv_lift1_eq … HU1 … HTU1) -HU1 #HU1 destruct
elim (cpys_inv_lift1_ge … HU2 … HLK … HTU1) -HU2 -HLK -HTU1 //
>yplus_minus_inj /2 width=3 by ex2_intro/
qed-.

(* Main properties **********************************************************)

theorem cpys_conf_eq: ∀G,L,T0,T1,l1,m1. ⦃G, L⦄ ⊢ T0 ▶*[l1, m1] T1 →
                      ∀T2,l2,m2. ⦃G, L⦄ ⊢ T0 ▶*[l2, m2] T2 →
                      ∃∃T. ⦃G, L⦄ ⊢ T1 ▶*[l2, m2] T & ⦃G, L⦄ ⊢ T2 ▶*[l1, m1] T.
normalize /3 width=3 by cpy_conf_eq, TC_confluent2/ qed-.

theorem cpys_conf_neq: ∀G,L1,T0,T1,l1,m1. ⦃G, L1⦄ ⊢ T0 ▶*[l1, m1] T1 →
                       ∀L2,T2,l2,m2. ⦃G, L2⦄ ⊢ T0 ▶*[l2, m2] T2 →
                       (l1 + m1 ≤ l2 ∨ l2 + m2 ≤ l1) →
                       ∃∃T. ⦃G, L2⦄ ⊢ T1 ▶*[l2, m2] T & ⦃G, L1⦄ ⊢ T2 ▶*[l1, m1] T.
normalize /3 width=3 by cpy_conf_neq, TC_confluent2/ qed-.

theorem cpys_trans_eq: ∀G,L,T1,T,T2,l,m.
                       ⦃G, L⦄ ⊢ T1 ▶*[l, m] T → ⦃G, L⦄ ⊢ T ▶*[l, m] T2 →
                       ⦃G, L⦄ ⊢ T1 ▶*[l, m] T2.
normalize /2 width=3 by trans_TC/ qed-.

theorem cpys_trans_down: ∀G,L,T1,T0,l1,m1. ⦃G, L⦄ ⊢ T1 ▶*[l1, m1] T0 →
                         ∀T2,l2,m2. ⦃G, L⦄ ⊢ T0 ▶*[l2, m2] T2 → l2 + m2 ≤ l1 →
                         ∃∃T. ⦃G, L⦄ ⊢ T1 ▶*[l2, m2] T & ⦃G, L⦄ ⊢ T ▶*[l1, m1] T2.
normalize /3 width=3 by cpy_trans_down, TC_transitive2/ qed-.

theorem cpys_antisym_eq: ∀G,L1,T1,T2,l,m. ⦃G, L1⦄ ⊢ T1 ▶*[l, m] T2 →
                         ∀L2. ⦃G, L2⦄ ⊢ T2 ▶*[l, m] T1 → T1 = T2.
#G #L1 #T1 #T2 #l #m #H @(cpys_ind_alt … H) -G -L1 -T1 -T2 //
[ #I1 #G #L1 #K1 #V1 #V2 #W2 #i #l #m #Hli #Hilm #_ #_ #HVW2 #_ #L2 #HW2
  elim (lt_or_ge (|L2|) (i+1)) #Hi [ -Hli -Hilm | ]
  [ lapply (cpys_weak_full … HW2) -HW2 #HW2
    lapply (cpys_weak … HW2 0 (i+1) ? ?) -HW2 //
    [ >yplus_O1 >yplus_O1 /3 width=1 by ylt_fwd_le, ylt_inj/ ] -Hi
    #HW2 >(cpys_inv_lift1_eq … HW2) -HW2 //
  | elim (drop_O1_le (Ⓕ) … Hi) -Hi #K2 #HLK2
    elim (cpys_inv_lift1_ge_up … HW2 … HLK2 … HVW2 ? ? ?) -HW2 -HLK2 -HVW2
    /2 width=1 by ylt_fwd_le_succ1, yle_succ_dx/ -Hli -Hilm
    #X #_ #H elim (lift_inv_lref2_be … H) -H /2 width=1 by ylt_inj/
  ]
| #a #I #G #L1 #V1 #V2 #T1 #T2 #l #m #_ #_ #IHV12 #IHT12 #L2 #H elim (cpys_inv_bind1 … H) -H
  #V #T #HV2 #HT2 #H destruct
  lapply (IHV12 … HV2) #H destruct -IHV12 -HV2 /3 width=2 by eq_f2/
| #I #G #L1 #V1 #V2 #T1 #T2 #l #m #_ #_ #IHV12 #IHT12 #L2 #H elim (cpys_inv_flat1 … H) -H
  #V #T #HV2 #HT2 #H destruct /3 width=2 by eq_f2/
]
qed-.
