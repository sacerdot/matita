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

include "ground_2/lib/ltc.ma".
include "basic_2/notation/relations/predstar_6.ma".
include "basic_2/notation/relations/predstar_5.ma".
include "basic_2/rt_transition/cpm.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS **************)

(* Basic_2A1: uses: scpds *)
definition cpms (h) (G) (L): relation3 nat term term ≝
                             ltc … plus … (cpm h G L).

interpretation
   "t-bound context-sensitive parallel rt-computarion (term)"
   'PRedStar n h G L T1 T2 = (cpms h G L n T1 T2).

interpretation
   "context-sensitive parallel r-computation (term)"
   'PRedStar h G L T1 T2 = (cpms h G L O T1 T2).

(* Basic eliminators ********************************************************)

lemma cpms_ind_sn (h) (G) (L) (T2) (Q:relation2 …):
                  Q 0 T2 →
                  (∀n1,n2,T1,T. ⦃G, L⦄ ⊢ T1 ➡[n1, h] T → ⦃G, L⦄ ⊢ T ➡*[n2, h] T2 → Q n2 T → Q (n1+n2) T1) →
                  ∀n,T1. ⦃G, L⦄ ⊢ T1 ➡*[n, h] T2 → Q n T1.
#h #G #L #T2 #R @ltc_ind_sn_refl //
qed-.

lemma cpms_ind_dx (h) (G) (L) (T1) (Q:relation2 …):
                  Q 0 T1 →
                  (∀n1,n2,T,T2. ⦃G, L⦄ ⊢ T1 ➡*[n1, h] T → Q n1 T → ⦃G, L⦄ ⊢ T ➡[n2, h] T2 → Q (n1+n2) T2) →
                  ∀n,T2. ⦃G, L⦄ ⊢ T1 ➡*[n, h] T2 → Q n T2.
#h #G #L #T1 #R @ltc_ind_dx_refl //
qed-.

(* Basic properties *********************************************************)

(* Basic_1: includes: pr1_pr0 *)
(* Basic_1: uses: pr3_pr2 *)
(* Basic_2A1: includes: cpr_cprs *)
lemma cpm_cpms (h) (G) (L): ∀n,T1,T2. ⦃G, L⦄ ⊢ T1 ➡[n, h] T2 → ⦃G, L⦄ ⊢ T1 ➡*[n, h] T2.
/2 width=1 by ltc_rc/ qed.

lemma cpms_step_sn (h) (G) (L): ∀n1,T1,T. ⦃G, L⦄ ⊢ T1 ➡[n1, h] T →
                                ∀n2,T2. ⦃G, L⦄ ⊢ T ➡*[n2, h] T2 → ⦃G, L⦄ ⊢ T1 ➡*[n1+n2, h] T2.
/2 width=3 by ltc_sn/ qed-.

lemma cpms_step_dx (h) (G) (L): ∀n1,T1,T. ⦃G, L⦄ ⊢ T1 ➡*[n1, h] T →
                                ∀n2,T2. ⦃G, L⦄ ⊢ T ➡[n2, h] T2 → ⦃G, L⦄ ⊢ T1 ➡*[n1+n2, h] T2.
/2 width=3 by ltc_dx/ qed-.

(* Basic_2A1: uses: cprs_bind_dx *)
lemma cpms_bind_dx (n) (h) (G) (L):
                   ∀V1,V2. ⦃G, L⦄ ⊢ V1 ➡[h] V2 →
                   ∀I,T1,T2. ⦃G, L.ⓑ{I}V1⦄ ⊢ T1 ➡*[n, h] T2 →
                   ∀p. ⦃G, L⦄ ⊢ ⓑ{p,I}V1.T1 ➡*[n, h] ⓑ{p,I}V2.T2.
#n #h #G #L #V1 #V2 #HV12 #I #T1 #T2 #H #a @(cpms_ind_sn … H) -T1
/3 width=3 by cpms_step_sn, cpm_cpms, cpm_bind/ qed.

(* Basic properties with r-transition ***************************************)

(* Basic_1: was: pr3_refl *)
lemma cprs_refl: ∀h,G,L. reflexive … (cpms h G L 0).
/2 width=1 by cpm_cpms/ qed.

(* Basic_2A1: removed theorems 4:
              sta_cprs_scpds lstas_scpds scpds_strap1 scpds_fwd_cprs
*)
