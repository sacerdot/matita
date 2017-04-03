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

include "basic_2/static/gcp_aaa.ma".
include "basic_2/rt_computation/cpxs_aaa.ma".
include "basic_2/rt_computation/csx_gcp.ma".
include "basic_2/rt_computation/csx_gcr.ma".

(* STRONGLY NORMALIZING TERMS FOR UNCOUNTED PARALLEL RT-TRANSITION **********)

(* Main properties with atomic arity assignment *****************************)

theorem aaa_csx: ∀h,o,G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T⦄.
#h #o #G #L #T #A #H
@(gcr_aaa … (csx_gcp h o) (csx_gcr h o) … H)
qed.

(* Advanced eliminators *****************************************************)

fact aaa_ind_csx_aux: ∀h,o,G,L,A. ∀R:predicate term.
                      (∀T1. ⦃G, L⦄ ⊢ T1 ⁝ A →
                            (∀T2. ⦃G, L⦄ ⊢ T1 ⬈[h] T2 → (T1 ≡[h, o] T2 → ⊥) → R T2) → R T1
                      ) →
                      ∀T. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T⦄ → ⦃G, L⦄ ⊢ T ⁝ A → R T.
#h #o #G #L #A #R #IH #T #H @(csx_ind … H) -T /4 width=5 by cpx_aaa_conf/
qed-.

lemma aaa_ind_csx: ∀h,o,G,L,A. ∀R:predicate term.
                   (∀T1. ⦃G, L⦄ ⊢ T1 ⁝ A →
                         (∀T2. ⦃G, L⦄ ⊢ T1 ⬈[h] T2 → (T1 ≡[h, o] T2 → ⊥) → R T2) → R T1
                   ) →
                   ∀T. ⦃G, L⦄ ⊢ T ⁝ A → R T.
/5 width=9 by aaa_ind_csx_aux, aaa_csx/ qed-.

fact aaa_ind_csx_cpxs_aux: ∀h,o,G,L,A. ∀R:predicate term.
                           (∀T1. ⦃G, L⦄ ⊢ T1 ⁝ A →
                                 (∀T2. ⦃G, L⦄ ⊢ T1 ⬈*[h] T2 → (T1 ≡[h, o] T2 → ⊥) → R T2) → R T1
                           ) →
                           ∀T. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T⦄ → ⦃G, L⦄ ⊢ T ⁝ A → R T.
#h #o #G #L #A #R #IH #T #H @(csx_ind_cpxs … H) -T /4 width=5 by cpxs_aaa_conf/
qed-.

(* Basic_2A1: was: aaa_ind_csx_alt *)
lemma aaa_ind_csx_cpxs: ∀h,o,G,L,A. ∀R:predicate term.
                        (∀T1. ⦃G, L⦄ ⊢ T1 ⁝ A →
                              (∀T2. ⦃G, L⦄ ⊢ T1 ⬈*[h] T2 → (T1 ≡[h, o] T2 → ⊥) → R T2) → R T1
                        ) →
                        ∀T. ⦃G, L⦄ ⊢ T ⁝ A → R T.
/5 width=9 by aaa_ind_csx_cpxs_aux, aaa_csx/ qed-.
