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

include "static_2/static/gcp_aaa.ma".
include "basic_2/rt_computation/cpxs_aaa.ma".
include "basic_2/rt_computation/csx_gcp.ma".
include "basic_2/rt_computation/csx_gcr.ma".

(* STRONGLY NORMALIZING TERMS FOR EXTENDED PARALLEL RT-TRANSITION ***********)

(* Main properties with atomic arity assignment *****************************)

theorem aaa_csx (G) (L):
        ∀T,A. ❨G,L❩ ⊢ T ⁝ A → ❨G,L❩ ⊢ ⬈*𝐒 T.
#G #L #T #A #H
@(gcr_aaa … csx_gcp csx_gcr … H)
qed.

(* Advanced eliminators *****************************************************)

fact aaa_ind_csx_aux (G) (L):
     ∀A. ∀Q:predicate ….
     (∀T1. ❨G,L❩ ⊢ T1 ⁝ A →
       (∀T2. ❨G,L❩ ⊢ T1 ⬈ T2 → (T1 ≅ T2 → ⊥) → Q T2) → Q T1
     ) →
     ∀T. ❨G,L❩ ⊢ ⬈*𝐒 T → ❨G,L❩ ⊢ T ⁝ A →  Q T.
#G #L #A #Q #IH #T #H @(csx_ind … H) -T /4 width=5 by cpx_aaa_conf/
qed-.

lemma aaa_ind_csx (G) (L):
      ∀A. ∀Q:predicate ….
      (∀T1. ❨G,L❩ ⊢ T1 ⁝ A →
        (∀T2. ❨G,L❩ ⊢ T1 ⬈ T2 → (T1 ≅ T2 → ⊥) → Q T2) → Q T1
      ) →
      ∀T. ❨G,L❩ ⊢ T ⁝ A → Q T.
/5 width=9 by aaa_ind_csx_aux, aaa_csx/ qed-.

fact aaa_ind_csx_cpxs_aux (G) (L):
     ∀A. ∀Q:predicate ….
     (∀T1. ❨G,L❩ ⊢ T1 ⁝ A →
       (∀T2. ❨G,L❩ ⊢ T1 ⬈* T2 → (T1 ≅ T2 → ⊥) → Q T2) → Q T1
     ) →
     ∀T. ❨G,L❩ ⊢ ⬈*𝐒 T → ❨G,L❩ ⊢ T ⁝ A →  Q T.
#G #L #A #Q #IH #T #H @(csx_ind_cpxs … H) -T /4 width=5 by cpxs_aaa_conf/
qed-.

(* Basic_2A1: was: aaa_ind_csx_alt *)
lemma aaa_ind_csx_cpxs (G) (L):
      ∀A. ∀Q:predicate ….
      (∀T1. ❨G,L❩ ⊢ T1 ⁝ A →
        (∀T2. ❨G,L❩ ⊢ T1 ⬈* T2 → (T1 ≅ T2 → ⊥) → Q T2) → Q T1
      ) →
      ∀T. ❨G,L❩ ⊢ T ⁝ A → Q T.
/5 width=9 by aaa_ind_csx_cpxs_aux, aaa_csx/ qed-.
