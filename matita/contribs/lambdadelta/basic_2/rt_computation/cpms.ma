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

(* Basic properties *********************************************************)

lemma cpm_cpms (h) (G) (L): ∀n,T1,T2. ⦃G, L⦄ ⊢ T1 ➡[n, h] T2 → ⦃G, L⦄ ⊢ T1 ➡*[n, h] T2.
/2 width=1 by ltc_rc/ qed.

lemma cpms_step_sn (h) (G) (L): ∀n1,T1,T. ⦃G, L⦄ ⊢ T1 ➡[n1, h] T →
                                ∀n2,T2. ⦃G, L⦄ ⊢ T ➡*[n2, h] T2 → ⦃G, L⦄ ⊢ T1 ➡*[n1+n2, h] T2.
/2 width=3 by ltc_sn/ qed-.

lemma cpms_step_dx (h) (G) (L): ∀n1,T1,T. ⦃G, L⦄ ⊢ T1 ➡*[n1, h] T →
                                ∀n2,T2. ⦃G, L⦄ ⊢ T ➡[n2, h] T2 → ⦃G, L⦄ ⊢ T1 ➡*[n1+n2, h] T2.
/2 width=3 by ltc_dx/ qed-.

(* Basic properties with r-transition ***************************************)

lemma cprs_refl: ∀h,G,L. reflexive … (cpms h G L 0).
/2 width=1 by cpm_cpms/ qed.

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

(* Basic_2A1: removed theorems 4:
              sta_cprs_scpds lstas_scpds scpds_strap1 scpds_fwd_cprs
*)
