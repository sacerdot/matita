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

include "ground_2/lib/star.ma".
include "basic_2/notation/relations/predtystar_5.ma".
include "basic_2/rt_transition/cpx.ma".

(* UNBOUND CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS **************)

definition cpxs: sh → relation4 genv lenv term term ≝
                 λh,G. CTC … (cpx h G).

interpretation "unbound context-sensitive parallel rt-computation (term)"
   'PRedTyStar h G L T1 T2 = (cpxs h G L T1 T2).

(* Basic eliminators ********************************************************)

lemma cpxs_ind: ∀h,G,L,T1. ∀Q:predicate term. Q T1 →
                (∀T,T2. ⦃G, L⦄ ⊢ T1 ⬈*[h] T → ⦃G, L⦄ ⊢ T ⬈[h] T2 → Q T → Q T2) →
                ∀T2. ⦃G, L⦄ ⊢ T1 ⬈*[h] T2 → Q T2.
#h #L #G #T1 #Q #HT1 #IHT1 #T2 #HT12
@(TC_star_ind … HT1 IHT1 … HT12) //
qed-.

lemma cpxs_ind_dx: ∀h,G,L,T2. ∀Q:predicate term. Q T2 →
                   (∀T1,T. ⦃G, L⦄ ⊢ T1 ⬈[h] T → ⦃G, L⦄ ⊢ T ⬈*[h] T2 → Q T → Q T1) →
                   ∀T1. ⦃G, L⦄ ⊢ T1 ⬈*[h] T2 → Q T1.
#h #G #L #T2 #Q #HT2 #IHT2 #T1 #HT12
@(TC_star_ind_dx … HT2 IHT2 … HT12) //
qed-.

(* Basic properties *********************************************************)

lemma cpxs_refl: ∀h,G,L,T. ⦃G, L⦄ ⊢ T ⬈*[h] T.
/2 width=1 by inj/ qed.

lemma cpx_cpxs: ∀h,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ⬈[h] T2 → ⦃G, L⦄ ⊢ T1 ⬈*[h] T2.
/2 width=1 by inj/ qed.

lemma cpxs_strap1: ∀h,G,L,T1,T. ⦃G, L⦄ ⊢ T1 ⬈*[h] T →
                   ∀T2. ⦃G, L⦄ ⊢ T ⬈[h] T2 → ⦃G, L⦄ ⊢ T1 ⬈*[h] T2.
normalize /2 width=3 by step/ qed-.

lemma cpxs_strap2: ∀h,G,L,T1,T. ⦃G, L⦄ ⊢ T1 ⬈[h] T →
                   ∀T2. ⦃G, L⦄ ⊢ T ⬈*[h] T2 → ⦃G, L⦄ ⊢ T1 ⬈*[h] T2.
normalize /2 width=3 by TC_strap/ qed-.

(* Basic_2A1: was just: cpxs_sort *)
lemma cpxs_sort: ∀h,G,L,s,n. ⦃G, L⦄ ⊢ ⋆s ⬈*[h] ⋆((next h)^n s).
#h #G #L #s #n elim n -n /2 width=1 by cpx_cpxs/
#n >iter_S /2 width=3 by cpxs_strap1/
qed.

lemma cpxs_bind_dx: ∀h,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ⬈[h] V2 →
                    ∀I,T1,T2. ⦃G, L. ⓑ{I}V1⦄ ⊢ T1 ⬈*[h] T2 →
                    ∀p. ⦃G, L⦄ ⊢ ⓑ{p,I}V1.T1 ⬈*[h] ⓑ{p,I}V2.T2.
#h #G #L #V1 #V2 #HV12 #I #T1 #T2 #HT12 #a @(cpxs_ind_dx … HT12) -T1
/3 width=3 by cpxs_strap2, cpx_cpxs, cpx_pair_sn, cpx_bind/
qed.

lemma cpxs_flat_dx: ∀h,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ⬈[h] V2 →
                    ∀T1,T2. ⦃G, L⦄ ⊢ T1 ⬈*[h] T2 →
                    ∀I. ⦃G, L⦄ ⊢ ⓕ{I}V1.T1 ⬈*[h] ⓕ{I}V2.T2.
#h #G #L #V1 #V2 #HV12 #T1 #T2 #HT12 @(cpxs_ind … HT12) -T2
/3 width=5 by cpxs_strap1, cpx_cpxs, cpx_pair_sn, cpx_flat/
qed.

lemma cpxs_flat_sn: ∀h,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ⬈[h] T2 →
                    ∀V1,V2. ⦃G, L⦄ ⊢ V1 ⬈*[h] V2 →
                    ∀I. ⦃G, L⦄ ⊢ ⓕ{I}V1.T1 ⬈*[h] ⓕ{I}V2.T2.
#h #G #L #T1 #T2 #HT12 #V1 #V2 #H @(cpxs_ind … H) -V2
/3 width=5 by cpxs_strap1, cpx_cpxs, cpx_pair_sn, cpx_flat/
qed.

lemma cpxs_pair_sn: ∀h,I,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ⬈*[h] V2 →
                    ∀T. ⦃G, L⦄ ⊢ ②{I}V1.T ⬈*[h] ②{I}V2.T.
#h #I #G #L #V1 #V2 #H @(cpxs_ind … H) -V2
/3 width=3 by cpxs_strap1, cpx_pair_sn/
qed.

lemma cpxs_zeta: ∀h,G,L,V,T1,T,T2. ⬆*[1] T2 ≘ T →
                 ⦃G, L.ⓓV⦄ ⊢ T1 ⬈*[h] T → ⦃G, L⦄ ⊢ +ⓓV.T1 ⬈*[h] T2.
#h #G #L #V #T1 #T #T2 #HT2 #H @(cpxs_ind_dx … H) -T1
/3 width=3 by cpxs_strap2, cpx_cpxs, cpx_bind, cpx_zeta/
qed.

lemma cpxs_eps: ∀h,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ⬈*[h] T2 →
                ∀V. ⦃G, L⦄ ⊢ ⓝV.T1 ⬈*[h] T2.
#h #G #L #T1 #T2 #H @(cpxs_ind … H) -T2
/3 width=3 by cpxs_strap1, cpx_cpxs, cpx_eps/
qed.

(* Basic_2A1: was: cpxs_ct *)
lemma cpxs_ee: ∀h,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ⬈*[h] V2 →
               ∀T. ⦃G, L⦄ ⊢ ⓝV1.T ⬈*[h] V2.
#h #G #L #V1 #V2 #H @(cpxs_ind … H) -V2
/3 width=3 by cpxs_strap1, cpx_cpxs, cpx_ee/
qed.

lemma cpxs_beta_dx: ∀h,p,G,L,V1,V2,W1,W2,T1,T2.
                    ⦃G, L⦄ ⊢ V1 ⬈[h] V2 → ⦃G, L.ⓛW1⦄ ⊢ T1 ⬈*[h] T2 → ⦃G, L⦄ ⊢ W1 ⬈[h] W2 →
                    ⦃G, L⦄ ⊢ ⓐV1.ⓛ{p}W1.T1 ⬈*[h] ⓓ{p}ⓝW2.V2.T2.
#h #p #G #L #V1 #V2 #W1 #W2 #T1 #T2 #HV12 * -T2
/4 width=7 by cpx_cpxs, cpxs_strap1, cpxs_bind_dx, cpxs_flat_dx, cpx_beta/
qed.

lemma cpxs_theta_dx: ∀h,p,G,L,V1,V,V2,W1,W2,T1,T2.
                     ⦃G, L⦄ ⊢ V1 ⬈[h] V → ⬆*[1] V ≘ V2 → ⦃G, L.ⓓW1⦄ ⊢ T1 ⬈*[h] T2 →
                     ⦃G, L⦄ ⊢ W1 ⬈[h] W2 → ⦃G, L⦄ ⊢ ⓐV1.ⓓ{p}W1.T1 ⬈*[h] ⓓ{p}W2.ⓐV2.T2.
#h #p #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #HV1 #HV2 * -T2 
/4 width=9 by cpx_cpxs, cpxs_strap1, cpxs_bind_dx, cpxs_flat_dx, cpx_theta/
qed.

(* Basic inversion lemmas ***************************************************)

(* Basic_2A1: wa just: cpxs_inv_sort1 *)
lemma cpxs_inv_sort1: ∀h,G,L,X2,s. ⦃G, L⦄ ⊢ ⋆s ⬈*[h] X2 →
                      ∃n. X2 = ⋆((next h)^n s).
#h #G #L #X2 #s #H @(cpxs_ind … H) -X2 /2 width=2 by ex_intro/
#X #X2 #_ #HX2 * #n #H destruct
elim (cpx_inv_sort1 … HX2) -HX2 #H destruct /2 width=2 by ex_intro/
@(ex_intro … (↑n)) >iter_S //
qed-.

lemma cpxs_inv_cast1: ∀h,G,L,W1,T1,U2. ⦃G, L⦄ ⊢ ⓝW1.T1 ⬈*[h] U2 →
                      ∨∨ ∃∃W2,T2. ⦃G, L⦄ ⊢ W1 ⬈*[h] W2 & ⦃G, L⦄ ⊢ T1 ⬈*[h] T2 & U2 = ⓝW2.T2
                       | ⦃G, L⦄ ⊢ T1 ⬈*[h] U2
                       | ⦃G, L⦄ ⊢ W1 ⬈*[h] U2.
#h #G #L #W1 #T1 #U2 #H @(cpxs_ind … H) -U2 /3 width=5 by or3_intro0, ex3_2_intro/
#U2 #U #_ #HU2 * /3 width=3 by cpxs_strap1, or3_intro1, or3_intro2/ *
#W #T #HW1 #HT1 #H destruct
elim (cpx_inv_cast1 … HU2) -HU2 /3 width=3 by cpxs_strap1, or3_intro1, or3_intro2/ *
#W2 #T2 #HW2 #HT2 #H destruct
lapply (cpxs_strap1 … HW1 … HW2) -W
lapply (cpxs_strap1 … HT1 … HT2) -T /3 width=5 by or3_intro0, ex3_2_intro/
qed-.
