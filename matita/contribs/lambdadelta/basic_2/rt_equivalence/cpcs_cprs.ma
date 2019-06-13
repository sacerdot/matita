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

include "basic_2/rt_computation/cprs_cprs.ma".
include "basic_2/rt_computation/lprs_cpms.ma".
include "basic_2/rt_equivalence/cpcs.ma".

(* CONTEXT-SENSITIVE PARALLEL R-EQUIVALENCE FOR TERMS ***********************)

(* Inversion lemmas with context sensitive r-computation on terms ***********)

lemma cpcs_inv_cprs (h) (G) (L): ∀T1,T2. ⦃G,L⦄ ⊢ T1 ⬌*[h] T2 →
                                 ∃∃T. ⦃G,L⦄ ⊢ T1 ➡*[h] T & ⦃G,L⦄ ⊢ T2 ➡*[h] T.
#h #G #L #T1 #T2 #H @(cpcs_ind_dx … H) -T2
[ /3 width=3 by ex2_intro/
| #T #T2 #_ #HT2 * #T0 #HT10 elim HT2 -HT2 #HT2 #HT0
  [ elim (cprs_strip … HT0 … HT2) -T /3 width=3 by cprs_step_dx, ex2_intro/
  | /3 width=5 by cprs_step_sn, ex2_intro/
  ]
]
qed-.

(* Advanced inversion lemmas ************************************************)

(* Basic_1: was: pc3_gen_sort *)
(* Basic_2A1: was: cpcs_inv_sort *)
lemma cpcs_inv_sort_bi (h) (G) (L): ∀s1,s2. ⦃G,L⦄ ⊢ ⋆s1 ⬌*[h] ⋆s2 → s1 = s2.
#h #G #L #s1 #s2 #H elim (cpcs_inv_cprs … H) -H
#T #H1 >(cprs_inv_sort1 … H1) -T #H2
lapply (cprs_inv_sort1 … H2) -L #H destruct //
qed-.

(* Basic_2A1: was: cpcs_inv_abst1 *)
lemma cpcs_inv_abst_sn (h) (G) (L):
                       ∀p,W1,T1,X. ⦃G,L⦄ ⊢ ⓛ{p}W1.T1 ⬌*[h] X →
                       ∃∃W2,T2. ⦃G,L⦄ ⊢ X ➡*[h] ⓛ{p}W2.T2 & ⦃G,L⦄ ⊢ ⓛ{p}W1.T1 ➡*[h] ⓛ{p}W2.T2.
#h #G #L #p #W1 #T1 #T #H
elim (cpcs_inv_cprs … H) -H #X #H1 #H2
elim (cpms_inv_abst_sn … H1) -H1 #W2 #T2 #HW12 #HT12 #H destruct
/3 width=6 by cpms_bind, ex2_2_intro/
qed-.

(* Basic_2A1: was: cpcs_inv_abst2 *)
lemma cpcs_inv_abst_dx (h) (G) (L):
                       ∀p,W1,T1,X. ⦃G,L⦄ ⊢ X ⬌*[h] ⓛ{p}W1.T1 →
                       ∃∃W2,T2. ⦃G,L⦄ ⊢ X ➡*[h] ⓛ{p}W2.T2 & ⦃G,L⦄ ⊢ ⓛ{p}W1.T1 ➡*[h] ⓛ{p}W2.T2.
/3 width=1 by cpcs_inv_abst_sn, cpcs_sym/ qed-.

(* Basic_1: was: pc3_gen_sort_abst *)
lemma cpcs_inv_sort_abst (h) (G) (L):
                         ∀p,W,T,s. ⦃G,L⦄ ⊢ ⋆s ⬌*[h] ⓛ{p}W.T → ⊥.
#h #G #L #p #W #T #s #H
elim (cpcs_inv_cprs … H) -H #X #H1
>(cprs_inv_sort1 … H1) -X #H2
elim (cpms_inv_abst_sn … H2) -H2 #W0 #T0 #_ #_ #H destruct
qed-.

(* Properties with context sensitive r-computation on terms *****************)

(* Basic_1: was: pc3_pr3_r *)
lemma cpcs_cprs_dx (h) (G) (L): ∀T1,T2. ⦃G,L⦄ ⊢ T1 ➡*[h] T2 → ⦃G,L⦄ ⊢ T1 ⬌*[h] T2.
#h #G #L #T1 #T2 #H @(cprs_ind_dx … H) -T2
/3 width=3 by cpcs_cpr_step_dx, cpcs_step_dx, cpc_cpcs/
qed.

(* Basic_1: was: pc3_pr3_x *)
lemma cpcs_cprs_sn (h) (G) (L): ∀T1,T2. ⦃G,L⦄ ⊢ T2 ➡*[h] T1 → ⦃G,L⦄ ⊢ T1 ⬌*[h] T2.
#h #G #L #T1 #T2 #H @(cprs_ind_sn … H) -T2
/3 width=3 by cpcs_cpr_div, cpcs_step_sn, cpcs_cprs_dx/
qed.

(* Basic_2A1: was: cpcs_cprs_strap1 *)
lemma cpcs_cprs_step_dx (h) (G) (L): ∀T1,T. ⦃G,L⦄ ⊢ T1 ⬌*[h] T →
                                     ∀T2. ⦃G,L⦄ ⊢ T ➡*[h] T2 → ⦃G,L⦄ ⊢ T1 ⬌*[h] T2.
#h #G #L #T1 #T #HT1 #T2 #H @(cprs_ind_dx … H) -T2 /2 width=3 by cpcs_cpr_step_dx/
qed-.

(* Basic_2A1: was: cpcs_cprs_strap2 *)
lemma cpcs_cprs_step_sn (h) (G) (L): ∀T1,T. ⦃G,L⦄ ⊢ T1 ➡*[h] T →
                                     ∀T2. ⦃G,L⦄ ⊢ T ⬌*[h] T2 → ⦃G,L⦄ ⊢ T1 ⬌*[h] T2.
#h #G #L #T1 #T #H #T2 #HT2 @(cprs_ind_sn … H) -T1 /2 width=3 by cpcs_cpr_step_sn/
qed-.

lemma cpcs_cprs_div (h) (G) (L): ∀T1,T. ⦃G,L⦄ ⊢ T1 ⬌*[h] T →
                                 ∀T2. ⦃G,L⦄ ⊢ T2 ➡*[h] T → ⦃G,L⦄ ⊢ T1 ⬌*[h] T2.
#h #G #L #T1 #T #HT1 #T2 #H @(cprs_ind_sn … H) -T2 /2 width=3 by cpcs_cpr_div/
qed-.

(* Basic_1: was: pc3_pr3_conf *)
lemma cpcs_cprs_conf (h) (G) (L): ∀T1,T. ⦃G,L⦄ ⊢ T ➡*[h] T1 →
                                  ∀T2. ⦃G,L⦄ ⊢ T ⬌*[h] T2 → ⦃G,L⦄ ⊢ T1 ⬌*[h] T2.
#h #G #L #T1 #T #H #T2 #HT2 @(cprs_ind_dx … H) -T1 /2 width=3 by cpcs_cpr_conf/
qed-.

(* Basic_1: was: pc3_pr3_t *)
(* Basic_1: note: pc3_pr3_t should be renamed *)
lemma cprs_div (h) (G) (L): ∀T1,T. ⦃G,L⦄ ⊢ T1 ➡*[h] T →
                            ∀T2. ⦃G,L⦄ ⊢ T2 ➡*[h] T → ⦃G,L⦄ ⊢ T1 ⬌*[h] T2.
#h #G #L #T1 #T #HT1 #T2 #H @(cprs_ind_sn … H) -T2
/2 width=3 by cpcs_cpr_div, cpcs_cprs_dx/
qed.

lemma cprs_cpr_div (h) (G) (L): ∀T1,T. ⦃G,L⦄ ⊢ T1 ➡*[h] T →
                                ∀T2. ⦃G,L⦄ ⊢ T2 ➡[h] T → ⦃G,L⦄ ⊢ T1 ⬌*[h] T2.
/3 width=5 by cpm_cpms, cprs_div/ qed-.

lemma cpr_cprs_div (h) (G) (L): ∀T1,T. ⦃G,L⦄ ⊢ T1 ➡[h] T →
                                ∀T2. ⦃G,L⦄ ⊢ T2 ➡*[h] T → ⦃G,L⦄ ⊢ T1 ⬌*[h] T2.
/3 width=3 by cpm_cpms, cprs_div/ qed-.

lemma cpr_cprs_conf_cpcs (h) (G) (L): ∀T,T1. ⦃G,L⦄ ⊢ T ➡*[h] T1 →
                                      ∀T2. ⦃G,L⦄ ⊢ T ➡[h] T2 → ⦃G,L⦄ ⊢ T1 ⬌*[h] T2.
#h #G #L #T #T1 #HT1 #T2 #HT2 elim (cprs_strip … HT1 … HT2) -HT1 -HT2
/2 width=3 by cpr_cprs_div/
qed-.

lemma cprs_cpr_conf_cpcs (h) (G) (L): ∀T,T1. ⦃G,L⦄ ⊢ T ➡*[h] T1 →
                                      ∀T2. ⦃G,L⦄ ⊢ T ➡[h] T2 → ⦃G,L⦄ ⊢ T2 ⬌*[h] T1.
#h #G #L #T #T1 #HT1 #T2 #HT2 elim (cprs_strip … HT1 … HT2) -HT1 -HT2
/2 width=3 by cprs_cpr_div/
qed-.

lemma cprs_conf_cpcs (h) (G) (L): ∀T,T1. ⦃G,L⦄ ⊢ T ➡*[h] T1 →
                                  ∀T2. ⦃G,L⦄ ⊢ T ➡*[h] T2 → ⦃G,L⦄ ⊢ T1 ⬌*[h] T2.
#h #G #L #T #T1 #HT1 #T2 #HT2 elim (cprs_conf … HT1 … HT2) -HT1 -HT2
/2 width=3 by cprs_div/
qed-.

(* Basic_1: was only: pc3_thin_dx *)
lemma cpcs_flat (h) (G) (L): ∀V1,V2. ⦃G,L⦄ ⊢ V1 ⬌*[h] V2 →
                             ∀T1,T2. ⦃G,L⦄ ⊢ T1 ⬌*[h] T2 →
                             ∀I. ⦃G,L⦄ ⊢ ⓕ{I}V1.T1 ⬌*[h] ⓕ{I}V2.T2.
#h #G #L #V1 #V2 #HV12 #T1 #T2 #HT12
elim (cpcs_inv_cprs … HV12) -HV12
elim (cpcs_inv_cprs … HT12) -HT12
/3 width=5 by cprs_flat, cprs_div/
qed.

lemma cpcs_flat_dx_cpr_rev (h) (G) (L): ∀V1,V2. ⦃G,L⦄ ⊢ V2 ➡[h] V1 →
                                        ∀T1,T2. ⦃G,L⦄ ⊢ T1 ⬌*[h] T2 →
                                        ∀I. ⦃G,L⦄ ⊢ ⓕ{I}V1.T1 ⬌*[h] ⓕ{I}V2.T2.
/3 width=1 by cpr_cpcs_sn, cpcs_flat/ qed.

lemma cpcs_bind_dx (h) (G) (L): ∀I,V,T1,T2. ⦃G,L.ⓑ{I}V⦄ ⊢ T1 ⬌*[h] T2 →
                                ∀p. ⦃G,L⦄ ⊢ ⓑ{p,I}V.T1 ⬌*[h] ⓑ{p,I}V.T2.
#h #G #L #I #V #T1 #T2 #HT12 elim (cpcs_inv_cprs … HT12) -HT12
/3 width=5 by cprs_div, cpms_bind/
qed.

lemma cpcs_bind_sn (h) (G) (L): ∀I,V1,V2,T. ⦃G,L⦄ ⊢ V1 ⬌*[h] V2 →
                                ∀p. ⦃G,L⦄ ⊢ ⓑ{p,I}V1.T ⬌*[h] ⓑ{p,I}V2.T.
#h #G #L #I #V1 #V2 #T #HV12 elim (cpcs_inv_cprs … HV12) -HV12
/3 width=5 by cprs_div, cpms_bind/
qed.
