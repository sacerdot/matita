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

include "ground/lib/star.ma".
include "basic_2/notation/relations/predtystar_4.ma".
include "basic_2/rt_transition/cpx.ma".

(* EXTENDED CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS *************)

definition cpxs (G): relation3 lenv term term ≝
           CTC … (cpx G).

interpretation
  "extended context-sensitive parallel rt-computation (term)"
  'PRedTyStar G L T1 T2 = (cpxs G L T1 T2).

(* Basic eliminators ********************************************************)

lemma cpxs_ind (G) (L) (T1) (Q:predicate …):
      Q T1 →
      (∀T,T2. ❨G,L❩ ⊢ T1 ⬈* T → ❨G,L❩ ⊢ T ⬈ T2 → Q T → Q T2) →
      ∀T2. ❨G,L❩ ⊢ T1 ⬈* T2 → Q T2.
#L #G #T1 #Q #HT1 #IHT1 #T2 #HT12
@(TC_star_ind … HT1 IHT1 … HT12) //
qed-.

lemma cpxs_ind_dx (G) (L) (T2) (Q:predicate …):
      Q T2 →
      (∀T1,T. ❨G,L❩ ⊢ T1 ⬈ T → ❨G,L❩ ⊢ T ⬈* T2 → Q T → Q T1) →
      ∀T1. ❨G,L❩ ⊢ T1 ⬈* T2 → Q T1.
#G #L #T2 #Q #HT2 #IHT2 #T1 #HT12
@(TC_star_ind_dx … HT2 IHT2 … HT12) //
qed-.

(* Basic properties *********************************************************)

lemma cpxs_refl (G) (L):
      ∀T. ❨G,L❩ ⊢ T ⬈* T.
/2 width=1 by inj/ qed.

lemma cpx_cpxs (G) (L): ∀T1,T2. ❨G,L❩ ⊢ T1 ⬈ T2 → ❨G,L❩ ⊢ T1 ⬈* T2.
/2 width=1 by inj/ qed.

lemma cpxs_strap1 (G) (L):
      ∀T1,T. ❨G,L❩ ⊢ T1 ⬈* T →
      ∀T2. ❨G,L❩ ⊢ T ⬈ T2 → ❨G,L❩ ⊢ T1 ⬈* T2.
normalize /2 width=3 by step/ qed-.

lemma cpxs_strap2 (G) (L):
      ∀T1,T. ❨G,L❩ ⊢ T1 ⬈ T →
      ∀T2. ❨G,L❩ ⊢ T ⬈* T2 → ❨G,L❩ ⊢ T1 ⬈* T2.
normalize /2 width=3 by TC_strap/ qed-.

(* Basic_2A1: was just: cpxs_sort *)
lemma cpxs_qu (G) (L):
      ∀s1,s2. ❨G,L❩ ⊢ ⋆s1 ⬈* ⋆s2.
/2 width=1 by cpx_cpxs/ qed.

lemma cpxs_bind_dx (G) (L):
      ∀V1,V2. ❨G,L❩ ⊢ V1 ⬈ V2 →
      ∀I,T1,T2. ❨G,L. ⓑ[I]V1❩ ⊢ T1 ⬈* T2 →
      ∀p. ❨G,L❩ ⊢ ⓑ[p,I]V1.T1 ⬈* ⓑ[p,I]V2.T2.
#G #L #V1 #V2 #HV12 #I #T1 #T2 #HT12 #a @(cpxs_ind_dx … HT12) -T1
/3 width=3 by cpxs_strap2, cpx_cpxs, cpx_pair_sn, cpx_bind/
qed.

lemma cpxs_flat_dx (G) (L):
      ∀V1,V2. ❨G,L❩ ⊢ V1 ⬈ V2 →
      ∀T1,T2. ❨G,L❩ ⊢ T1 ⬈* T2 →
      ∀I. ❨G,L❩ ⊢ ⓕ[I]V1.T1 ⬈* ⓕ[I]V2.T2.
#G #L #V1 #V2 #HV12 #T1 #T2 #HT12 @(cpxs_ind … HT12) -T2
/3 width=5 by cpxs_strap1, cpx_cpxs, cpx_pair_sn, cpx_flat/
qed.

lemma cpxs_flat_sn (G) (L):
      ∀T1,T2. ❨G,L❩ ⊢ T1 ⬈ T2 →
      ∀V1,V2. ❨G,L❩ ⊢ V1 ⬈* V2 →
      ∀I. ❨G,L❩ ⊢ ⓕ[I]V1.T1 ⬈* ⓕ[I]V2.T2.
#G #L #T1 #T2 #HT12 #V1 #V2 #H @(cpxs_ind … H) -V2
/3 width=5 by cpxs_strap1, cpx_cpxs, cpx_pair_sn, cpx_flat/
qed.

lemma cpxs_pair_sn (G) (L):
      ∀I,V1,V2. ❨G,L❩ ⊢ V1 ⬈* V2 →
      ∀T. ❨G,L❩ ⊢ ②[I]V1.T ⬈* ②[I]V2.T.
#G #L #I #V1 #V2 #H @(cpxs_ind … H) -V2
/3 width=3 by cpxs_strap1, cpx_pair_sn/
qed.

lemma cpxs_zeta (G) (L) (V):
      ∀T1,T. ⇧[1] T ≘ T1 →
      ∀T2. ❨G,L❩ ⊢ T ⬈* T2 → ❨G,L❩ ⊢ +ⓓV.T1 ⬈* T2.
#G #L #V #T1 #T #HT1 #T2 #H @(cpxs_ind … H) -T2
/3 width=3 by cpxs_strap1, cpx_cpxs, cpx_zeta/
qed.

(* Basic_2A1: was: cpxs_zeta *)
lemma cpxs_zeta_dx (G) (L) (V):
      ∀T2,T. ⇧[1] T2 ≘ T →
      ∀T1. ❨G,L.ⓓV❩ ⊢ T1 ⬈* T → ❨G,L❩ ⊢ +ⓓV.T1 ⬈* T2.
#G #L #V #T2 #T #HT2 #T1 #H @(cpxs_ind_dx … H) -T1
/3 width=3 by cpxs_strap2, cpx_cpxs, cpx_bind, cpx_zeta/
qed.

lemma cpxs_eps (G) (L):
      ∀T1,T2. ❨G,L❩ ⊢ T1 ⬈* T2 →
      ∀V. ❨G,L❩ ⊢ ⓝV.T1 ⬈* T2.
#G #L #T1 #T2 #H @(cpxs_ind … H) -T2
/3 width=3 by cpxs_strap1, cpx_cpxs, cpx_eps/
qed.

(* Basic_2A1: was: cpxs_ct *)
lemma cpxs_ee (G) (L):
      ∀V1,V2. ❨G,L❩ ⊢ V1 ⬈* V2 →
      ∀T. ❨G,L❩ ⊢ ⓝV1.T ⬈* V2.
#G #L #V1 #V2 #H @(cpxs_ind … H) -V2
/3 width=3 by cpxs_strap1, cpx_cpxs, cpx_ee/
qed.

lemma cpxs_beta_dx (G) (L):
      ∀p,V1,V2,W1,W2,T1,T2.
      ❨G,L❩ ⊢ V1 ⬈ V2 → ❨G,L.ⓛW1❩ ⊢ T1 ⬈* T2 → ❨G,L❩ ⊢ W1 ⬈ W2 →
      ❨G,L❩ ⊢ ⓐV1.ⓛ[p]W1.T1 ⬈* ⓓ[p]ⓝW2.V2.T2.
#G #L #p #V1 #V2 #W1 #W2 #T1 #T2 #HV12 * -T2
/4 width=7 by cpx_cpxs, cpxs_strap1, cpxs_bind_dx, cpxs_flat_dx, cpx_beta/
qed.

lemma cpxs_theta_dx (G) (L):
      ∀p,V1,V,V2,W1,W2,T1,T2.
      ❨G,L❩ ⊢ V1 ⬈ V → ⇧[1] V ≘ V2 → ❨G,L.ⓓW1❩ ⊢ T1 ⬈* T2 →
      ❨G,L❩ ⊢ W1 ⬈ W2 → ❨G,L❩ ⊢ ⓐV1.ⓓ[p]W1.T1 ⬈* ⓓ[p]W2.ⓐV2.T2.
#G #L #p #V1 #V #V2 #W1 #W2 #T1 #T2 #HV1 #HV2 * -T2
/4 width=9 by cpx_cpxs, cpxs_strap1, cpxs_bind_dx, cpxs_flat_dx, cpx_theta/
qed.

(* Basic inversion lemmas ***************************************************)

(* Basic_2A1: wa just: cpxs_inv_sort1 *)
lemma cpxs_inv_sort1 (G) (L):
      ∀X2,s1. ❨G,L❩ ⊢ ⋆s1 ⬈* X2 →
      ∃s2. X2 = ⋆s2.
#G #L #X2 #s1 #H @(cpxs_ind … H) -X2 /2 width=2 by ex_intro/
#X #X2 #_ #HX2 * #s #H destruct
elim (cpx_inv_sort1 … HX2) -HX2 #s2 #H destruct /2 width=2 by ex_intro/
qed-.

lemma cpxs_inv_cast1 (G) (L):
      ∀W1,T1,U2. ❨G,L❩ ⊢ ⓝW1.T1 ⬈* U2 →
      ∨∨ ∃∃W2,T2. ❨G,L❩ ⊢ W1 ⬈* W2 & ❨G,L❩ ⊢ T1 ⬈* T2 & U2 = ⓝW2.T2
       | ❨G,L❩ ⊢ T1 ⬈* U2
       | ❨G,L❩ ⊢ W1 ⬈* U2.
#G #L #W1 #T1 #U2 #H @(cpxs_ind … H) -U2 /3 width=5 by or3_intro0, ex3_2_intro/
#U2 #U #_ #HU2 * /3 width=3 by cpxs_strap1, or3_intro1, or3_intro2/ *
#W #T #HW1 #HT1 #H destruct
elim (cpx_inv_cast1 … HU2) -HU2 /3 width=3 by cpxs_strap1, or3_intro1, or3_intro2/ *
#W2 #T2 #HW2 #HT2 #H destruct
lapply (cpxs_strap1 … HW1 … HW2) -W
lapply (cpxs_strap1 … HT1 … HT2) -T /3 width=5 by or3_intro0, ex3_2_intro/
qed-.
