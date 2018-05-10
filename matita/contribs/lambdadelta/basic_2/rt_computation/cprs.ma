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

include "basic_2/rt_transition/cpr.ma".
include "basic_2/rt_computation/cpms.ma".

(* CONTEXT-SENSITIVE PARALLEL COMPUTATION FOR TERMS *************************)

(* Basic eliminators ********************************************************)

(* Basic_2A1: was: cprs_ind_dx *)
lemma cprs_ind_sn (h) (G) (L) (T2) (R:predicate …):
                  R T2 →
                  (∀T1,T. ⦃G, L⦄ ⊢ T1 ➡[h] T → ⦃G, L⦄ ⊢ T ➡*[h] T2 → R T → R T1) →
                  ∀T1. ⦃G, L⦄ ⊢ T1 ➡*[h] T2 → R T1.
#h #G #L #T2 #R #IH1 #IH2 #T1
@(insert_eq_0 … 0) #n #H
@(cpms_ind_sn … H) -n -T1 //
#n1 #n2 #T1 #T #HT1 #HT2 #IH #H
elim (plus_inv_O3 n1 n2) // -H #H1 #H2 destruct
/3 width=4 by/
qed-.

(* Basic_2A1: was: cprs_ind *)
lemma cprs_ind_dx (h) (G) (L) (T1) (R:predicate …):
                  R T1 →
                  (∀T,T2. ⦃G, L⦄ ⊢ T1 ➡*[h] T → ⦃G, L⦄ ⊢ T ➡[h] T2 → R T → R T2) →
                  ∀T2. ⦃G, L⦄ ⊢ T1 ➡*[h] T2 → R T2.
#h #G #L #T1 #R #IH1 #IH2 #T2
@(insert_eq_0 … 0) #n #H
@(cpms_ind_dx … H) -n -T2 //
#n1 #n2 #T #T2 #HT1 #IH #HT2 #H
elim (plus_inv_O3 n1 n2) // -H #H1 #H2 destruct
/3 width=4 by/
qed-.

(* Basic properties *********************************************************)

(* Basic_1: was: pr3_step *)
(* Basic_2A1: was: cprs_strap2 *)
lemma cprs_step_sn (h) (G) (L):
                   ∀T1,T. ⦃G, L⦄ ⊢ T1 ➡[h] T →
                   ∀T2. ⦃G, L⦄ ⊢ T ➡*[h] T2 → ⦃G, L⦄ ⊢ T1 ➡*[h] T2.
/2 width=3 by cpms_step_sn/ qed-.

(* Basic_2A1: was: cprs_strap1 *)
lemma cprs_step_dx (h) (G) (L):
                   ∀T1,T. ⦃G, L⦄ ⊢ T1 ➡*[h] T →
                   ∀T2. ⦃G, L⦄ ⊢ T ➡[h] T2 → ⦃G, L⦄ ⊢ T1 ➡*[h] T2.
/2 width=3 by cpms_step_dx/ qed-.

(* Basic_1: was only: pr3_thin_dx *)
lemma cprs_flat_dx (h) (I) (G) (L):
                   ∀V1,V2. ⦃G, L⦄ ⊢ V1 ➡[h] V2 →
                   ∀T1,T2. ⦃G, L⦄ ⊢ T1 ➡*[h] T2 →
                   ⦃G, L⦄ ⊢ ⓕ{I}V1.T1 ➡*[h] ⓕ{I}V2.T2.
#h #I #G #L #V1 #V2 #HV12 #T1 #T2 #H @(cprs_ind_sn … H) -T1
/3 width=3 by cprs_step_sn, cpm_cpms, cpr_flat/
qed.
(*
lemma cprs_flat_sn: ∀I,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡[h] T2 → ∀V1,V2. ⦃G, L⦄ ⊢ V1 ➡*[h] V2 →
                    ⦃G, L⦄ ⊢ ⓕ{I} V1. T1 ➡*[h] ⓕ{I} V2. T2.
#I #G #L #T1 #T2 #HT12 #V1 #V2 #H @(cprs_ind … H) -V2
/3 width=3 by cprs_strap1, cpr_cprs, cpr_pair_sn, cpr_flat/
qed.

lemma cprs_zeta: ∀G,L,V,T1,T,T2. ⬆[0, 1] T2 ≘ T →
                 ⦃G, L.ⓓV⦄ ⊢ T1 ➡*[h] T → ⦃G, L⦄ ⊢ +ⓓV.T1 ➡*[h] T2.
#G #L #V #T1 #T #T2 #HT2 #H @(cprs_ind_dx … H) -T1
/3 width=3 by cprs_strap2, cpr_cprs, cpr_bind, cpr_zeta/
qed.

lemma cprs_eps: ∀G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡*[h] T2 → ∀V. ⦃G, L⦄ ⊢ ⓝV.T1 ➡*[h] T2.
#G #L #T1 #T2 #H @(cprs_ind … H) -T2
/3 width=3 by cprs_strap1, cpr_cprs, cpr_eps/
qed.

lemma cprs_beta_dx: ∀a,G,L,V1,V2,W1,W2,T1,T2.
                    ⦃G, L⦄ ⊢ V1 ➡[h] V2 → ⦃G, L⦄ ⊢ W1 ➡[h] W2 → ⦃G, L.ⓛW1⦄ ⊢ T1 ➡*[h] T2 →
                    ⦃G, L⦄ ⊢ ⓐV1.ⓛ{a}W1.T1 ➡*[h] ⓓ{a}ⓝW2.V2.T2.
#a #G #L #V1 #V2 #W1 #W2 #T1 #T2 #HV12 #HW12 * -T2
/4 width=7 by cprs_strap1, cpr_cprs, cprs_bind_dx, cprs_flat_dx, cpr_beta/
qed.

lemma cprs_theta_dx: ∀a,G,L,V1,V,V2,W1,W2,T1,T2.
                     ⦃G, L⦄ ⊢ V1 ➡[h] V → ⬆[0, 1] V ≘ V2 → ⦃G, L.ⓓW1⦄ ⊢ T1 ➡*[h] T2 →
                     ⦃G, L⦄ ⊢ W1 ➡[h] W2 → ⦃G, L⦄ ⊢ ⓐV1.ⓓ{a}W1.T1 ➡*[h] ⓓ{a}W2.ⓐV2.T2.
#a #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #HV1 #HV2 * -T2
/4 width=9 by cprs_strap1, cpr_cprs, cprs_bind_dx, cprs_flat_dx, cpr_theta/
qed.

(* Basic inversion lemmas ***************************************************)

(* Basic_1: was: pr3_gen_sort *)
lemma cprs_inv_sort1: ∀G,L,U2,s. ⦃G, L⦄ ⊢ ⋆s ➡*[h] U2 → U2 = ⋆s.
#G #L #U2 #s #H @(cprs_ind … H) -U2 //
#U2 #U #_ #HU2 #IHU2 destruct
>(cpr_inv_sort1 … HU2) -HU2 //
qed-.

(* Basic_1: was: pr3_gen_cast *)
lemma cprs_inv_cast1: ∀G,L,W1,T1,U2. ⦃G, L⦄ ⊢ ⓝW1.T1 ➡*[h] U2 → ⦃G, L⦄ ⊢ T1 ➡*[h] U2 ∨
                      ∃∃W2,T2. ⦃G, L⦄ ⊢ W1 ➡*[h] W2 & ⦃G, L⦄ ⊢ T1 ➡*[h] T2 & U2 = ⓝW2.T2.
#G #L #W1 #T1 #U2 #H @(cprs_ind … H) -U2 /3 width=5 by ex3_2_intro, or_intror/
#U2 #U #_ #HU2 * /3 width=3 by cprs_strap1, or_introl/ *
#W #T #HW1 #HT1 #H destruct
elim (cpr_inv_cast1 … HU2) -HU2 /3 width=3 by cprs_strap1, or_introl/ *
#W2 #T2 #HW2 #HT2 #H destruct /4 width=5 by cprs_strap1, ex3_2_intro, or_intror/
qed-.
*)
(* Basic_1: removed theorems 13:
   pr1_head_1 pr1_head_2 pr1_comp
   clear_pr3_trans pr3_cflat pr3_gen_bind
   pr3_head_1 pr3_head_2 pr3_head_21 pr3_head_12
   pr3_iso_appl_bind pr3_iso_appls_appl_bind pr3_iso_appls_bind
*)
