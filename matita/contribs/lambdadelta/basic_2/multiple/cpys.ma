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

include "basic_2/notation/relations/psubststar_6.ma".
include "basic_2/substitution/cpy.ma".

(* CONTEXT-SENSITIVE EXTENDED MULTIPLE SUBSTITUTION FOR TERMS ***************)

definition cpys: ynat → ynat → relation4 genv lenv term term ≝
                 λl,m,G. LTC … (cpy l m G).

interpretation "context-sensitive extended multiple substritution (term)"
   'PSubstStar G L T1 l m T2 = (cpys l m G L T1 T2).

(* Basic eliminators ********************************************************)

lemma cpys_ind: ∀G,L,T1,l,m. ∀R:predicate term. R T1 →
                (∀T,T2. ⦃G, L⦄ ⊢ T1 ▶*[l, m] T → ⦃G, L⦄ ⊢ T ▶[l, m] T2 → R T → R T2) →
                ∀T2. ⦃G, L⦄ ⊢ T1 ▶*[l, m] T2 → R T2.
#G #L #T1 #l #m #R #HT1 #IHT1 #T2 #HT12
@(TC_star_ind … HT1 IHT1 … HT12) //
qed-.

lemma cpys_ind_dx: ∀G,L,T2,l,m. ∀R:predicate term. R T2 →
                   (∀T1,T. ⦃G, L⦄ ⊢ T1 ▶[l, m] T → ⦃G, L⦄ ⊢ T ▶*[l, m] T2 → R T → R T1) →
                   ∀T1. ⦃G, L⦄ ⊢ T1 ▶*[l, m] T2 → R T1.
#G #L #T2 #l #m #R #HT2 #IHT2 #T1 #HT12
@(TC_star_ind_dx … HT2 IHT2 … HT12) //
qed-.

(* Basic properties *********************************************************)

lemma cpy_cpys: ∀G,L,T1,T2,l,m. ⦃G, L⦄ ⊢ T1 ▶[l, m] T2 → ⦃G, L⦄ ⊢ T1 ▶*[l, m] T2.
/2 width=1 by inj/ qed.

lemma cpys_strap1: ∀G,L,T1,T,T2,l,m.
                   ⦃G, L⦄ ⊢ T1 ▶*[l, m] T → ⦃G, L⦄ ⊢ T ▶[l, m] T2 → ⦃G, L⦄ ⊢ T1 ▶*[l, m] T2.
normalize /2 width=3 by step/ qed-.

lemma cpys_strap2: ∀G,L,T1,T,T2,l,m.
                   ⦃G, L⦄ ⊢ T1 ▶[l, m] T → ⦃G, L⦄ ⊢ T ▶*[l, m] T2 → ⦃G, L⦄ ⊢ T1 ▶*[l, m] T2.
normalize /2 width=3 by TC_strap/ qed-.

lemma lsuby_cpys_trans: ∀G,l,m. lsub_trans … (cpys l m G) (lsuby l m).
/3 width=5 by lsuby_cpy_trans, LTC_lsub_trans/
qed-.

lemma cpys_refl: ∀G,L,l,m. reflexive … (cpys l m G L).
/2 width=1 by cpy_cpys/ qed.

lemma cpys_bind: ∀G,L,V1,V2,l,m. ⦃G, L⦄ ⊢ V1 ▶*[l, m] V2 →
                 ∀I,T1,T2. ⦃G, L.ⓑ{I}V1⦄ ⊢ T1 ▶*[⫯l, m] T2 →
                 ∀a. ⦃G, L⦄ ⊢ ⓑ{a,I}V1.T1 ▶*[l, m] ⓑ{a,I}V2.T2.
#G #L #V1 #V2 #l #m #HV12 @(cpys_ind … HV12) -V2
[ #I #T1 #T2 #HT12 @(cpys_ind … HT12) -T2 /3 width=5 by cpys_strap1, cpy_bind/
| /3 width=5 by cpys_strap1, cpy_bind/
]
qed.

lemma cpys_flat: ∀G,L,V1,V2,l,m. ⦃G, L⦄ ⊢ V1 ▶*[l, m] V2 →
                 ∀T1,T2. ⦃G, L⦄ ⊢ T1 ▶*[l, m] T2 →
                 ∀I. ⦃G, L⦄ ⊢ ⓕ{I}V1.T1 ▶*[l, m] ⓕ{I}V2.T2.
#G #L #V1 #V2 #l #m #HV12 @(cpys_ind … HV12) -V2
[ #T1 #T2 #HT12 @(cpys_ind … HT12) -T2 /3 width=5 by cpys_strap1, cpy_flat/
| /3 width=5 by cpys_strap1, cpy_flat/
qed.

lemma cpys_weak: ∀G,L,T1,T2,l1,m1. ⦃G, L⦄ ⊢ T1 ▶*[l1, m1] T2 →
                 ∀l2,m2. l2 ≤ l1 → l1 + m1 ≤ l2 + m2 →
                 ⦃G, L⦄ ⊢ T1 ▶*[l2, m2] T2.
#G #L #T1 #T2 #l1 #m1 #H #l1 #l2 #Hl21 #Hlm12 @(cpys_ind … H) -T2
/3 width=7 by cpys_strap1, cpy_weak/
qed-.

lemma cpys_weak_top: ∀G,L,T1,T2,l,m.
                     ⦃G, L⦄ ⊢ T1 ▶*[l, m] T2 → ⦃G, L⦄ ⊢ T1 ▶*[l, |L| - l] T2.
#G #L #T1 #T2 #l #m #H @(cpys_ind … H) -T2
/3 width=4 by cpys_strap1, cpy_weak_top/
qed-.

lemma cpys_weak_full: ∀G,L,T1,T2,l,m.
                      ⦃G, L⦄ ⊢ T1 ▶*[l, m] T2 → ⦃G, L⦄ ⊢ T1 ▶*[0, |L|] T2.
#G #L #T1 #T2 #l #m #H @(cpys_ind … H) -T2
/3 width=5 by cpys_strap1, cpy_weak_full/
qed-.

(* Basic forward lemmas *****************************************************)

lemma cpys_fwd_up: ∀G,L,U1,U2,lt,mt. ⦃G, L⦄ ⊢ U1 ▶*[lt, mt] U2 →
                   ∀T1,l,m. ⬆[l, m] T1 ≡ U1 →
                   l ≤ lt → l + m ≤ lt + mt →
                   ∃∃T2. ⦃G, L⦄ ⊢ U1 ▶*[l+m, lt+mt-(l+m)] U2 & ⬆[l, m] T2 ≡ U2.
#G #L #U1 #U2 #lt #mt #H #T1 #l #m #HTU1 #Hllt #Hlmlmt @(cpys_ind … H) -U2
[ /2 width=3 by ex2_intro/
| -HTU1 #U #U2 #_ #HU2 * #T #HU1 #HTU
  elim (cpy_fwd_up … HU2 … HTU) -HU2 -HTU /3 width=3 by cpys_strap1, ex2_intro/
]
qed-.

lemma cpys_fwd_tw: ∀G,L,T1,T2,l,m. ⦃G, L⦄ ⊢ T1 ▶*[l, m] T2 → ♯{T1} ≤ ♯{T2}.
#G #L #T1 #T2 #l #m #H @(cpys_ind … H) -T2 //
#T #T2 #_ #HT2 #IHT1 lapply (cpy_fwd_tw … HT2) -HT2
/2 width=3 by transitive_le/
qed-.

(* Basic inversion lemmas ***************************************************)

(* Note: this can be derived from cpys_inv_atom1 *)
lemma cpys_inv_sort1: ∀G,L,T2,k,l,m. ⦃G, L⦄ ⊢ ⋆k ▶*[l, m] T2 → T2 = ⋆k.
#G #L #T2 #k #l #m #H @(cpys_ind … H) -T2 //
#T #T2 #_ #HT2 #IHT1 destruct
>(cpy_inv_sort1 … HT2) -HT2 //
qed-.

(* Note: this can be derived from cpys_inv_atom1 *)
lemma cpys_inv_gref1: ∀G,L,T2,p,l,m. ⦃G, L⦄ ⊢ §p ▶*[l, m] T2 → T2 = §p.
#G #L #T2 #p #l #m #H @(cpys_ind … H) -T2 //
#T #T2 #_ #HT2 #IHT1 destruct
>(cpy_inv_gref1 … HT2) -HT2 //
qed-.

lemma cpys_inv_bind1: ∀a,I,G,L,V1,T1,U2,l,m. ⦃G, L⦄ ⊢ ⓑ{a,I}V1.T1 ▶*[l, m] U2 →
                      ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ▶*[l, m] V2 &
                               ⦃G, L.ⓑ{I}V1⦄ ⊢ T1 ▶*[⫯l, m] T2 &
                               U2 = ⓑ{a,I}V2.T2.
#a #I #G #L #V1 #T1 #U2 #l #m #H @(cpys_ind … H) -U2
[ /2 width=5 by ex3_2_intro/
| #U #U2 #_ #HU2 * #V #T #HV1 #HT1 #H destruct
  elim (cpy_inv_bind1 … HU2) -HU2 #V2 #T2 #HV2 #HT2 #H
  lapply (lsuby_cpy_trans … HT2 (L.ⓑ{I}V1) ?) -HT2
  /3 width=5 by cpys_strap1, lsuby_succ, ex3_2_intro/
]
qed-.

lemma cpys_inv_flat1: ∀I,G,L,V1,T1,U2,l,m. ⦃G, L⦄ ⊢ ⓕ{I}V1.T1 ▶*[l, m] U2 →
                      ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ▶*[l, m] V2 & ⦃G, L⦄ ⊢ T1 ▶*[l, m] T2 &
                               U2 = ⓕ{I}V2.T2.
#I #G #L #V1 #T1 #U2 #l #m #H @(cpys_ind … H) -U2
[ /2 width=5 by ex3_2_intro/
| #U #U2 #_ #HU2 * #V #T #HV1 #HT1 #H destruct
  elim (cpy_inv_flat1 … HU2) -HU2
  /3 width=5 by cpys_strap1, ex3_2_intro/
]
qed-.

lemma cpys_inv_refl_O2: ∀G,L,T1,T2,l. ⦃G, L⦄ ⊢ T1 ▶*[l, 0] T2 → T1 = T2.
#G #L #T1 #T2 #l #H @(cpys_ind … H) -T2 //
#T #T2 #_ #HT2 #IHT1 <(cpy_inv_refl_O2 … HT2) -HT2 //
qed-.

lemma cpys_inv_lift1_eq: ∀G,L,U1,U2. ∀l,m:nat.
                         ⦃G, L⦄ ⊢ U1 ▶*[l, m] U2 → ∀T1. ⬆[l, m] T1 ≡ U1 → U1 = U2.
#G #L #U1 #U2 #l #m #H #T1 #HTU1 @(cpys_ind … H) -U2
/2 width=7 by cpy_inv_lift1_eq/
qed-.
