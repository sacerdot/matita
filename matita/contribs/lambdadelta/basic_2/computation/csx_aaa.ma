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

include "basic_2/computation/gcp_aaa.ma".
include "basic_2/computation/cpxs_aaa.ma".
include "basic_2/computation/csx_tsts_vector.ma".

(* CONTEXT-SENSITIVE EXTENDED STRONGLY NORMALIZING TERMS ********************)

(* Main properties on atomic arity assignment *******************************)

theorem aaa_csx: ∀h,g,G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → ⦃G, L⦄ ⊢ ⬊*[h, g] T.
#h #g #G #L #T #A #H
@(gcr_aaa … (csx_gcp h g) (csx_gcr h g) … H)
qed.

(* Advanced eliminators *****************************************************)

fact aaa_ind_csx_aux: ∀h,g,G,L,A. ∀R:predicate term.
                      (∀T1. ⦃G, L⦄ ⊢ T1 ⁝ A →
                            (∀T2. ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 → (T1 = T2 → ⊥) → R T2) → R T1
                      ) →
                      ∀T. ⦃G, L⦄ ⊢ ⬊*[h, g] T → ⦃G, L⦄ ⊢ T ⁝ A → R T.
#h #g #G #L #A #R #IH #T #H @(csx_ind … H) -T /4 width=5 by cpx_aaa_conf/
qed-.

lemma aaa_ind_csx: ∀h,g,G,L,A. ∀R:predicate term.
                   (∀T1. ⦃G, L⦄ ⊢ T1 ⁝ A →
                         (∀T2. ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 → (T1 = T2 → ⊥) → R T2) → R T1
                   ) →
                   ∀T. ⦃G, L⦄ ⊢ T ⁝ A → R T.
/5 width=9 by aaa_ind_csx_aux, aaa_csx/ qed-.

fact aaa_ind_csx_alt_aux: ∀h,g,G,L,A. ∀R:predicate term.
                          (∀T1. ⦃G, L⦄ ⊢ T1 ⁝ A →
                                (∀T2. ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2 → (T1 = T2 → ⊥) → R T2) → R T1
                          ) →
                          ∀T. ⦃G, L⦄ ⊢ ⬊*[h, g] T → ⦃G, L⦄ ⊢ T ⁝ A → R T.
#h #g #G #L #A #R #IH #T #H @(csx_ind_alt … H) -T /4 width=5 by cpxs_aaa_conf/
qed-.

lemma aaa_ind_csx_alt: ∀h,g,G,L,A. ∀R:predicate term.
                       (∀T1. ⦃G, L⦄ ⊢ T1 ⁝ A →
                             (∀T2. ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2 → (T1 = T2 → ⊥) → R T2) → R T1
                       ) →
                       ∀T. ⦃G, L⦄ ⊢ T ⁝ A → R T.
/5 width=9 by aaa_ind_csx_alt_aux, aaa_csx/ qed-.
