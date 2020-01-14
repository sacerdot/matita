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

(* CONTEXT-SENSITIVE PARALLEL R-COMPUTATION FOR TERMS ***********************)

(* Basic eliminators ********************************************************)

(* Basic_2A1: was: cprs_ind_dx *)
lemma cprs_ind_sn (h) (G) (L) (T2) (Q:predicate …):
                  Q T2 →
                  (∀T1,T. ❪G,L❫ ⊢ T1 ➡[h,0] T → ❪G,L❫ ⊢ T ➡*[h,0] T2 → Q T → Q T1) →
                  ∀T1. ❪G,L❫ ⊢ T1 ➡*[h,0] T2 → Q T1.
#h #G #L #T2 #Q #IH1 #IH2 #T1
@(insert_eq_0 … 0) #n #H
@(cpms_ind_sn … H) -n -T1 //
#n1 #n2 #T1 #T #HT1 #HT2 #IH #H
elim (plus_inv_O3 n1 n2) // -H #H1 #H2 destruct
/3 width=4 by/
qed-.

(* Basic_2A1: was: cprs_ind *)
lemma cprs_ind_dx (h) (G) (L) (T1) (Q:predicate …):
                  Q T1 →
                  (∀T,T2. ❪G,L❫ ⊢ T1 ➡*[h,0] T → ❪G,L❫ ⊢ T ➡[h,0] T2 → Q T → Q T2) →
                  ∀T2. ❪G,L❫ ⊢ T1 ➡*[h,0] T2 → Q T2.
#h #G #L #T1 #Q #IH1 #IH2 #T2
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
                   ∀T1,T. ❪G,L❫ ⊢ T1 ➡[h,0] T →
                   ∀T2. ❪G,L❫ ⊢ T ➡*[h,0] T2 → ❪G,L❫ ⊢ T1 ➡*[h,0] T2.
/2 width=3 by cpms_step_sn/ qed-.

(* Basic_2A1: was: cprs_strap1 *)
lemma cprs_step_dx (h) (G) (L):
                   ∀T1,T. ❪G,L❫ ⊢ T1 ➡*[h,0] T →
                   ∀T2. ❪G,L❫ ⊢ T ➡[h,0] T2 → ❪G,L❫ ⊢ T1 ➡*[h,0] T2.
/2 width=3 by cpms_step_dx/ qed-.

(* Basic_1: was only: pr3_thin_dx *)
lemma cprs_flat_dx (h) (I) (G) (L):
                   ∀V1,V2. ❪G,L❫ ⊢ V1 ➡[h,0] V2 →
                   ∀T1,T2. ❪G,L❫ ⊢ T1 ➡*[h,0] T2 →
                   ❪G,L❫ ⊢ ⓕ[I]V1.T1 ➡*[h,0] ⓕ[I]V2.T2.
#h #I #G #L #V1 #V2 #HV12 #T1 #T2 #H @(cprs_ind_sn … H) -T1
/3 width=3 by cprs_step_sn, cpm_cpms, cpr_flat/
qed.

lemma cprs_flat_sn (h) (I) (G) (L):
                   ∀T1,T2. ❪G,L❫ ⊢ T1 ➡[h,0] T2 → ∀V1,V2. ❪G,L❫ ⊢ V1 ➡*[h,0] V2 →
                   ❪G,L❫ ⊢ ⓕ[I] V1. T1 ➡*[h,0] ⓕ[I] V2. T2.
#h #I #G #L #T1 #T2 #HT12 #V1 #V2 #H @(cprs_ind_sn … H) -V1
/3 width=3 by cprs_step_sn, cpm_cpms, cpr_flat/
qed.

(* Basic inversion lemmas ***************************************************)

(* Basic_1: was: pr3_gen_sort *)
lemma cprs_inv_sort1 (h) (G) (L): ∀X2,s. ❪G,L❫ ⊢ ⋆s ➡*[h,0] X2 → X2 = ⋆s.
/2 width=4 by cpms_inv_sort1/ qed-.

(* Basic_1: was: pr3_gen_cast *)
lemma cprs_inv_cast1 (h) (G) (L): ∀W1,T1,X2. ❪G,L❫ ⊢ ⓝW1.T1 ➡*[h,0] X2 →
                                  ∨∨ ∃∃W2,T2. ❪G,L❫ ⊢ W1 ➡*[h,0] W2 & ❪G,L❫ ⊢ T1 ➡*[h,0] T2 & X2 = ⓝW2.T2
                                   | ❪G,L❫ ⊢ T1 ➡*[h,0] X2.
#h #G #L #W1 #T1 #X2 #H
elim (cpms_inv_cast1 … H) -H
[ /2 width=1 by or_introl/
| /2 width=1 by or_intror/
| * #m #_ #H destruct
]
qed-.

(* Basic_1: removed theorems 13:
   pr1_head_1 pr1_head_2 pr1_comp
   clear_pr3_trans pr3_cflat pr3_gen_bind
   pr3_head_1 pr3_head_2 pr3_head_21 pr3_head_12
   pr3_iso_appl_bind pr3_iso_appls_appl_bind pr3_iso_appls_bind
*)
