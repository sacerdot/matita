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

include "basic_2/rt_computation/cpxs_teqg.ma".
include "basic_2/rt_computation/cpxs_cpxs.ma".
include "basic_2/rt_computation/csx_csx.ma".

(* STRONGLY NORMALIZING TERMS FOR EXTENDED PARALLEL RT-TRANSITION ***********)

(* Properties with extended context-sensitive rt-computation for terms ******)

(* Basic_1: was just: sn3_intro *)
lemma csx_intro_cpxs (G) (L):
      ∀T1. (∀T2. ❨G,L❩ ⊢ T1 ⬈* T2 → (T1 ≅ T2 → ⊥) → ❨G,L❩ ⊢ ⬈*𝐒 T2) →
      ❨G,L❩ ⊢ ⬈*𝐒 T1.
/4 width=1 by cpx_cpxs, csx_intro/ qed-.

(* Basic_1: was just: sn3_pr3_trans *)
lemma csx_cpxs_trans (G) (L):
      ∀T1. ❨G,L❩ ⊢ ⬈*𝐒 T1 →
      ∀T2. ❨G,L❩ ⊢ T1 ⬈* T2 → ❨G,L❩ ⊢ ⬈*𝐒 T2.
#G #L #T1 #HT1 #T2 #H @(cpxs_ind … H) -T2
/2 width=3 by csx_cpx_trans/
qed-.

(* Eliminators with extended context-sensitive rt-computation for terms *****)

fact csx_ind_cpxs_aux (G) (L):
     ∀Q:predicate term.
     (∀T1. ❨G,L❩ ⊢ ⬈*𝐒 T1 →
       (∀T2. ❨G,L❩ ⊢ T1 ⬈* T2 → (T1 ≅ T2 → ⊥) → Q T2) → Q T1
     ) →
     ∀T1. ❨G,L❩ ⊢ ⬈*𝐒 T1 →
     ∀T2. ❨G,L❩ ⊢ T1 ⬈* T2 → Q T2.
#G #L #Q #IH #T1 #H @(csx_ind … H) -T1
#T1 #HT1 #IH1 #T2 #HT12
@IH -IH /2 width=3 by csx_cpxs_trans/ -HT1 #V2 #HTV2 #HnTV2
elim (teqx_dec T1 T2) #H
[ lapply (teqg_tneqg_trans … H … HnTV2) // -H -HnTV2 #Hn12
  lapply (cpxs_trans … HT12 … HTV2) -T2 #H12
  elim (cpxs_tneqg_fwd_step_sn … H12 …  Hn12) /2 width=1 by sfull_dec/ -H12 -Hn12
  /3 width=4 by/
| elim (cpxs_tneqg_fwd_step_sn … HT12 … H) -HT12 -H
  /3 width=6 by cpxs_trans, sfull_dec/
]
qed-.

(* Basic_2A1: was: csx_ind_alt *)
lemma csx_ind_cpxs (G) (L) (Q:predicate …):
      (∀T1. ❨G,L❩ ⊢ ⬈*𝐒 T1 →
        (∀T2. ❨G,L❩ ⊢ T1 ⬈* T2 → (T1 ≅ T2 → ⊥) → Q T2) → Q T1
      ) →
      ∀T. ❨G,L❩ ⊢ ⬈*𝐒 T → Q T.
#G #L #Q #IH #T #HT
@(csx_ind_cpxs_aux … IH … HT) -IH -HT // (**) (* full auto fails *)
qed-.
