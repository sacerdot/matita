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

include "basic_2/computation/lprs_cprs.ma".
include "basic_2/conversion/cpc_cpc.ma".
include "basic_2/equivalence/cpcs_cprs.ma".

(* CONTEXT-SENSITIVE PARALLEL EQUIVALENCE ON TERMS **************************)

(* Advanced inversion lemmas ************************************************)

lemma cpcs_inv_cprs: ∀G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ⬌* T2 →
                     ∃∃T. ⦃G, L⦄ ⊢ T1 ➡* T & ⦃G, L⦄ ⊢ T2 ➡* T.
#G #L #T1 #T2 #H @(cpcs_ind … H) -T2
[ /3 width=3 by ex2_intro/
| #T #T2 #_ #HT2 * #T0 #HT10 elim HT2 -HT2 #HT2 #HT0
  [ elim (cprs_strip … HT0 … HT2) -T /3 width=3 by cprs_strap1, ex2_intro/
  | /3 width=5 by cprs_strap2, ex2_intro/
  ]
]
qed-.

(* Basic_1: was: pc3_gen_sort *)
lemma cpcs_inv_sort: ∀G,L,k1,k2. ⦃G, L⦄ ⊢ ⋆k1 ⬌* ⋆k2 → k1 = k2.
#G #L #k1 #k2 #H elim (cpcs_inv_cprs … H) -H
#T #H1 >(cprs_inv_sort1 … H1) -T #H2
lapply (cprs_inv_sort1 … H2) -L #H destruct //
qed-.

lemma cpcs_inv_abst1: ∀a,G,L,W1,T1,T. ⦃G, L⦄ ⊢ ⓛ{a}W1.T1 ⬌* T →
                      ∃∃W2,T2. ⦃G, L⦄ ⊢ T ➡* ⓛ{a}W2.T2 & ⦃G, L⦄ ⊢ ⓛ{a}W1.T1 ➡* ⓛ{a}W2.T2.
#a #G #L #W1 #T1 #T #H
elim (cpcs_inv_cprs … H) -H #X #H1 #H2
elim (cprs_inv_abst1 … H1) -H1 #W2 #T2 #HW12 #HT12 #H destruct
/3 width=6 by cprs_bind, ex2_2_intro/
qed-.

lemma cpcs_inv_abst2: ∀a,G,L,W1,T1,T. ⦃G, L⦄ ⊢ T ⬌* ⓛ{a}W1.T1 →
                      ∃∃W2,T2. ⦃G, L⦄ ⊢ T ➡* ⓛ{a}W2.T2 & ⦃G, L⦄ ⊢ ⓛ{a}W1.T1 ➡* ⓛ{a}W2.T2.
/3 width=1 by cpcs_inv_abst1, cpcs_sym/ qed-.

(* Basic_1: was: pc3_gen_sort_abst *)
lemma cpcs_inv_sort_abst: ∀a,G,L,W,T,k. ⦃G, L⦄ ⊢ ⋆k ⬌* ⓛ{a}W.T → ⊥.
#a #G #L #W #T #k #H
elim (cpcs_inv_cprs … H) -H #X #H1
>(cprs_inv_sort1 … H1) -X #H2
elim (cprs_inv_abst1 … H2) -H2 #W0 #T0 #_ #_ #H destruct
qed-.

(* Basic_1: was: pc3_gen_lift *)
lemma cpcs_inv_lift: ∀G,L,K,s,d,e. ⇩[s, d, e] L ≡ K →
                     ∀T1,U1. ⇧[d, e] T1 ≡ U1 → ∀T2,U2. ⇧[d, e] T2 ≡ U2 →
                     ⦃G, L⦄ ⊢ U1 ⬌* U2 → ⦃G, K⦄ ⊢ T1 ⬌* T2.
#G #L #K #s #d #e #HLK #T1 #U1 #HTU1 #T2 #U2 #HTU2 #HU12
elim (cpcs_inv_cprs … HU12) -HU12 #U #HU1 #HU2
elim (cprs_inv_lift1 … HU1 … HLK … HTU1) -U1 #T #HTU #HT1
elim (cprs_inv_lift1 … HU2 … HLK … HTU2) -L -U2 #X #HXU
>(lift_inj … HXU … HTU) -X -U -d -e /2 width=3 by cprs_div/
qed-.

(* Advanced properties ******************************************************)

lemma lpr_cpcs_trans: ∀G,L1,L2. ⦃G, L1⦄ ⊢ ➡ L2 →
                      ∀T1,T2. ⦃G, L2⦄ ⊢ T1 ⬌* T2 → ⦃G, L1⦄ ⊢ T1 ⬌* T2.
#G #L1 #L2 #HL12 #T1 #T2 #H elim (cpcs_inv_cprs … H) -H
/4 width=5 by cprs_div, lpr_cprs_trans/
qed-.

lemma lprs_cpcs_trans: ∀G,L1,L2. ⦃G, L1⦄ ⊢ ➡* L2 →
                       ∀T1,T2. ⦃G, L2⦄ ⊢ T1 ⬌* T2 → ⦃G, L1⦄ ⊢ T1 ⬌* T2.
#G #L1 #L2 #HL12 #T1 #T2 #H elim (cpcs_inv_cprs … H) -H
/4 width=5 by cprs_div, lprs_cprs_trans/
qed-.

lemma cpr_cprs_conf_cpcs: ∀G,L,T,T1,T2. ⦃G, L⦄ ⊢ T ➡* T1 → ⦃G, L⦄ ⊢ T ➡ T2 → ⦃G, L⦄ ⊢ T1 ⬌* T2.
#G #L #T #T1 #T2 #HT1 #HT2 elim (cprs_strip … HT1 … HT2) -HT1 -HT2
/2 width=3 by cpr_cprs_div/
qed-.

lemma cprs_cpr_conf_cpcs: ∀G,L,T,T1,T2. ⦃G, L⦄ ⊢ T ➡* T1 → ⦃G, L⦄ ⊢ T ➡ T2 → ⦃G, L⦄ ⊢ T2 ⬌* T1.
#G #L #T #T1 #T2 #HT1 #HT2 elim (cprs_strip … HT1 … HT2) -HT1 -HT2
/2 width=3 by cprs_cpr_div/
qed-.

lemma cprs_conf_cpcs: ∀G,L,T,T1,T2. ⦃G, L⦄ ⊢ T ➡* T1 → ⦃G, L⦄ ⊢ T ➡* T2 → ⦃G, L⦄ ⊢ T1 ⬌* T2.
#G #L #T #T1 #T2 #HT1 #HT2 elim (cprs_conf … HT1 … HT2) -HT1 -HT2
/2 width=3 by cprs_div/
qed-.

lemma lprs_cprs_conf: ∀G,L1,L2. ⦃G, L1⦄ ⊢ ➡* L2 →
                      ∀T1,T2. ⦃G, L1⦄ ⊢ T1 ➡* T2 → ⦃G, L2⦄ ⊢ T1 ⬌* T2.
#G #L1 #L2 #HL12 #T1 #T2 #HT12 elim (lprs_cprs_conf_dx … HT12 … HL12) -L1
/2 width=3 by cprs_div/
qed-.

(* Basic_1: was: pc3_wcpr0_t *)
(* Basic_1: note: pc3_wcpr0_t should be renamed *)
(* Note: alternative proof /3 width=5 by lprs_cprs_conf, lpr_lprs/ *)
lemma lpr_cprs_conf: ∀G,L1,L2. ⦃G, L1⦄ ⊢ ➡ L2 →
                     ∀T1,T2. ⦃G, L1⦄ ⊢ T1 ➡* T2 → ⦃G, L2⦄ ⊢ T1 ⬌* T2.
#G #L1 #L2 #HL12 #T1 #T2 #HT12 elim (cprs_lpr_conf_dx … HT12 … HL12) -L1
/2 width=3 by cprs_div/
qed-.

(* Basic_1: was only: pc3_pr0_pr2_t *)
(* Basic_1: note: pc3_pr0_pr2_t should be renamed *)
lemma lpr_cpr_conf: ∀G,L1,L2. ⦃G, L1⦄ ⊢ ➡ L2 →
                    ∀T1,T2. ⦃G, L1⦄ ⊢ T1 ➡ T2 → ⦃G, L2⦄ ⊢ T1 ⬌* T2.
/3 width=5 by lpr_cprs_conf, cpr_cprs/ qed-.

(* Basic_1: was only: pc3_thin_dx *)
lemma cpcs_flat: ∀G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ⬌* V2 → ∀T1,T2. ⦃G, L⦄ ⊢ T1 ⬌* T2 →
                 ∀I. ⦃G, L⦄ ⊢ ⓕ{I}V1.T1 ⬌* ⓕ{I}V2.T2.
#G #L #V1 #V2 #HV12 #T1 #T2 #HT12
elim (cpcs_inv_cprs … HV12) -HV12
elim (cpcs_inv_cprs … HT12) -HT12
/3 width=5 by cprs_flat, cprs_div/
qed.

lemma cpcs_flat_dx_cpr_rev: ∀G,L,V1,V2. ⦃G, L⦄ ⊢ V2 ➡ V1 → ∀T1,T2. ⦃G, L⦄ ⊢ T1 ⬌* T2 →
                            ∀I. ⦃G, L⦄ ⊢ ⓕ{I}V1.T1 ⬌* ⓕ{I}V2.T2.
/3 width=1 by cpr_cpcs_sn, cpcs_flat/ qed.

lemma cpcs_bind_dx: ∀a,I,G,L,V,T1,T2. ⦃G, L.ⓑ{I}V⦄ ⊢ T1 ⬌* T2 →
                    ⦃G, L⦄ ⊢ ⓑ{a,I}V.T1 ⬌* ⓑ{a,I}V.T2.
#a #I #G #L #V #T1 #T2 #HT12 elim (cpcs_inv_cprs … HT12) -HT12
/3 width=5 by cprs_div, cprs_bind/
qed.

lemma cpcs_bind_sn: ∀a,I,G,L,V1,V2,T. ⦃G, L⦄ ⊢ V1 ⬌* V2 → ⦃G, L⦄ ⊢ ⓑ{a,I}V1. T ⬌* ⓑ{a,I}V2. T.
#a #I #G #L #V1 #V2 #T #HV12 elim (cpcs_inv_cprs … HV12) -HV12
/3 width=5 by cprs_div, cprs_bind/
qed.

lemma lsubr_cpcs_trans: ∀G,L1,T1,T2. ⦃G, L1⦄ ⊢ T1 ⬌* T2 →
                        ∀L2. L2 ⫃ L1 → ⦃G, L2⦄ ⊢ T1 ⬌* T2.
#G #L1 #T1 #T2 #HT12 elim (cpcs_inv_cprs … HT12) -HT12
/3 width=5 by cprs_div, lsubr_cprs_trans/
qed-.

(* Basic_1: was: pc3_lift *)
lemma cpcs_lift: ∀G,L,K,s,d,e. ⇩[s, d, e] L ≡ K →
                 ∀T1,U1. ⇧[d, e] T1 ≡ U1 → ∀T2,U2. ⇧[d, e] T2 ≡ U2 →
                 ⦃G, K⦄ ⊢ T1 ⬌* T2 → ⦃G, L⦄ ⊢ U1 ⬌* U2.
#G #L #K #s #d #e #HLK #T1 #U1 #HTU1 #T2 #U2 #HTU2 #HT12
elim (cpcs_inv_cprs … HT12) -HT12 #T #HT1 #HT2
elim (lift_total T d e) /3 width=12 by cprs_div, cprs_lift/
qed.

lemma cpcs_strip: ∀G,L,T1,T. ⦃G, L⦄ ⊢ T ⬌* T1 → ∀T2. ⦃G, L⦄ ⊢ T ⬌ T2 →
                  ∃∃T0. ⦃G, L⦄ ⊢ T1 ⬌ T0 & ⦃G, L⦄ ⊢ T2 ⬌* T0.
#G #L #T1 #T @TC_strip1 /2 width=3 by cpc_conf/ qed-.

(* More inversion lemmas ****************************************************)

(* Note: there must be a proof suitable for llpr *)
lemma cpcs_inv_abst_sn: ∀a1,a2,G,L,W1,W2,T1,T2. ⦃G, L⦄ ⊢ ⓛ{a1}W1.T1 ⬌* ⓛ{a2}W2.T2 →
                        ∧∧ ⦃G, L⦄ ⊢ W1 ⬌* W2 & ⦃G, L.ⓛW1⦄ ⊢ T1 ⬌* T2 & a1 = a2.
#a1 #a2 #G #L #W1 #W2 #T1 #T2 #H
elim (cpcs_inv_cprs … H) -H #T #H1 #H2
elim (cprs_inv_abst1 … H1) -H1 #W0 #T0 #HW10 #HT10 #H destruct
elim (cprs_inv_abst1 … H2) -H2 #W #T #HW2 #HT2 #H destruct
lapply (lprs_cprs_conf … (L.ⓛW) … HT2) /2 width=1 by lprs_pair/ -HT2 #HT2
lapply (lprs_cpcs_trans … (L.ⓛW1) … HT2) /2 width=1 by lprs_pair/ -HT2 #HT2
/4 width=3 by and3_intro, cprs_div, cpcs_cprs_div, cpcs_sym/
qed-.

lemma cpcs_inv_abst_dx: ∀a1,a2,G,L,W1,W2,T1,T2. ⦃G, L⦄ ⊢ ⓛ{a1}W1.T1 ⬌* ⓛ{a2}W2.T2 →
                        ∧∧ ⦃G, L⦄ ⊢ W1 ⬌* W2 & ⦃G, L.ⓛW2⦄ ⊢ T1 ⬌* T2 & a1 = a2.
#a1 #a2 #G #L #W1 #W2 #T1 #T2 #HT12 lapply (cpcs_sym … HT12) -HT12
#HT12 elim (cpcs_inv_abst_sn … HT12) -HT12 /3 width=1 by cpcs_sym, and3_intro/
qed-.

(* Main properties **********************************************************)

(* Basic_1: was pc3_t *)
theorem cpcs_trans: ∀G,L,T1,T. ⦃G, L⦄ ⊢ T1 ⬌* T → ∀T2. ⦃G, L⦄ ⊢ T ⬌* T2 → ⦃G, L⦄ ⊢ T1 ⬌* T2.
#G #L #T1 #T #HT1 #T2 @(trans_TC … HT1) qed-.

theorem cpcs_canc_sn: ∀G,L,T,T1,T2. ⦃G, L⦄ ⊢ T ⬌* T1 → ⦃G, L⦄ ⊢ T ⬌* T2 → ⦃G, L⦄ ⊢ T1 ⬌* T2.
/3 width=3 by cpcs_trans, cpcs_sym/ qed-.

theorem cpcs_canc_dx: ∀G,L,T,T1,T2. ⦃G, L⦄ ⊢ T1 ⬌* T → ⦃G, L⦄ ⊢ T2 ⬌* T → ⦃G, L⦄ ⊢ T1 ⬌* T2.
/3 width=3 by cpcs_trans, cpcs_sym/ qed-.

lemma cpcs_bind1: ∀a,I,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ⬌* V2 →
                  ∀T1,T2. ⦃G, L.ⓑ{I}V1⦄ ⊢ T1 ⬌* T2 →
                  ⦃G, L⦄ ⊢ ⓑ{a,I}V1. T1 ⬌* ⓑ{a,I}V2. T2.
/3 width=3 by cpcs_trans, cpcs_bind_sn, cpcs_bind_dx/ qed.

lemma cpcs_bind2: ∀a,I,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ⬌* V2 →
                  ∀T1,T2. ⦃G, L.ⓑ{I}V2⦄ ⊢ T1 ⬌* T2 →
                  ⦃G, L⦄ ⊢ ⓑ{a,I}V1. T1 ⬌* ⓑ{a,I}V2. T2.
/3 width=3 by cpcs_trans, cpcs_bind_sn, cpcs_bind_dx/ qed.

(* Basic_1: was: pc3_wcpr0 *)
lemma lpr_cpcs_conf: ∀G,L1,L2. ⦃G, L1⦄ ⊢ ➡ L2 →
                     ∀T1,T2. ⦃G, L1⦄ ⊢ T1 ⬌* T2 → ⦃G, L2⦄ ⊢ T1 ⬌* T2.
#G #L1 #L2 #HL12 #T1 #T2 #H elim (cpcs_inv_cprs … H) -H
/3 width=5 by cpcs_canc_dx, lpr_cprs_conf/
qed-.
