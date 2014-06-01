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
                 λd,e,G. LTC … (cpy d e G).

interpretation "context-sensitive extended multiple substritution (term)"
   'PSubstStar G L T1 d e T2 = (cpys d e G L T1 T2).

(* Basic eliminators ********************************************************)

lemma cpys_ind: ∀G,L,T1,d,e. ∀R:predicate term. R T1 →
                (∀T,T2. ⦃G, L⦄ ⊢ T1 ▶*[d, e] T → ⦃G, L⦄ ⊢ T ▶[d, e] T2 → R T → R T2) →
                ∀T2. ⦃G, L⦄ ⊢ T1 ▶*[d, e] T2 → R T2.
#G #L #T1 #d #e #R #HT1 #IHT1 #T2 #HT12
@(TC_star_ind … HT1 IHT1 … HT12) //
qed-.

lemma cpys_ind_dx: ∀G,L,T2,d,e. ∀R:predicate term. R T2 →
                   (∀T1,T. ⦃G, L⦄ ⊢ T1 ▶[d, e] T → ⦃G, L⦄ ⊢ T ▶*[d, e] T2 → R T → R T1) →
                   ∀T1. ⦃G, L⦄ ⊢ T1 ▶*[d, e] T2 → R T1.
#G #L #T2 #d #e #R #HT2 #IHT2 #T1 #HT12
@(TC_star_ind_dx … HT2 IHT2 … HT12) //
qed-.

(* Basic properties *********************************************************)

lemma cpy_cpys: ∀G,L,T1,T2,d,e. ⦃G, L⦄ ⊢ T1 ▶[d, e] T2 → ⦃G, L⦄ ⊢ T1 ▶*[d, e] T2.
/2 width=1 by inj/ qed.

lemma cpys_strap1: ∀G,L,T1,T,T2,d,e.
                   ⦃G, L⦄ ⊢ T1 ▶*[d, e] T → ⦃G, L⦄ ⊢ T ▶[d, e] T2 → ⦃G, L⦄ ⊢ T1 ▶*[d, e] T2.
normalize /2 width=3 by step/ qed-.

lemma cpys_strap2: ∀G,L,T1,T,T2,d,e.
                   ⦃G, L⦄ ⊢ T1 ▶[d, e] T → ⦃G, L⦄ ⊢ T ▶*[d, e] T2 → ⦃G, L⦄ ⊢ T1 ▶*[d, e] T2.
normalize /2 width=3 by TC_strap/ qed-.

lemma lsuby_cpys_trans: ∀G,d,e. lsub_trans … (cpys d e G) (lsuby d e).
/3 width=5 by lsuby_cpy_trans, LTC_lsub_trans/
qed-.

lemma cpys_refl: ∀G,L,d,e. reflexive … (cpys d e G L).
/2 width=1 by cpy_cpys/ qed.

lemma cpys_bind: ∀G,L,V1,V2,d,e. ⦃G, L⦄ ⊢ V1 ▶*[d, e] V2 →
                 ∀I,T1,T2. ⦃G, L.ⓑ{I}V1⦄ ⊢ T1 ▶*[⫯d, e] T2 →
                 ∀a. ⦃G, L⦄ ⊢ ⓑ{a,I}V1.T1 ▶*[d, e] ⓑ{a,I}V2.T2.
#G #L #V1 #V2 #d #e #HV12 @(cpys_ind … HV12) -V2
[ #I #T1 #T2 #HT12 @(cpys_ind … HT12) -T2 /3 width=5 by cpys_strap1, cpy_bind/
| /3 width=5 by cpys_strap1, cpy_bind/
]
qed.

lemma cpys_flat: ∀G,L,V1,V2,d,e. ⦃G, L⦄ ⊢ V1 ▶*[d, e] V2 →
                 ∀T1,T2. ⦃G, L⦄ ⊢ T1 ▶*[d, e] T2 →
                 ∀I. ⦃G, L⦄ ⊢ ⓕ{I}V1.T1 ▶*[d, e] ⓕ{I}V2.T2.
#G #L #V1 #V2 #d #e #HV12 @(cpys_ind … HV12) -V2
[ #T1 #T2 #HT12 @(cpys_ind … HT12) -T2 /3 width=5 by cpys_strap1, cpy_flat/
| /3 width=5 by cpys_strap1, cpy_flat/
qed.

lemma cpys_weak: ∀G,L,T1,T2,d1,e1. ⦃G, L⦄ ⊢ T1 ▶*[d1, e1] T2 →
                 ∀d2,e2. d2 ≤ d1 → d1 + e1 ≤ d2 + e2 →
                 ⦃G, L⦄ ⊢ T1 ▶*[d2, e2] T2.
#G #L #T1 #T2 #d1 #e1 #H #d1 #d2 #Hd21 #Hde12 @(cpys_ind … H) -T2
/3 width=7 by cpys_strap1, cpy_weak/
qed-.

lemma cpys_weak_top: ∀G,L,T1,T2,d,e.
                     ⦃G, L⦄ ⊢ T1 ▶*[d, e] T2 → ⦃G, L⦄ ⊢ T1 ▶*[d, |L| - d] T2.
#G #L #T1 #T2 #d #e #H @(cpys_ind … H) -T2
/3 width=4 by cpys_strap1, cpy_weak_top/
qed-.

lemma cpys_weak_full: ∀G,L,T1,T2,d,e.
                      ⦃G, L⦄ ⊢ T1 ▶*[d, e] T2 → ⦃G, L⦄ ⊢ T1 ▶*[0, |L|] T2.
#G #L #T1 #T2 #d #e #H @(cpys_ind … H) -T2
/3 width=5 by cpys_strap1, cpy_weak_full/
qed-.

(* Basic forward lemmas *****************************************************)

lemma cpys_fwd_up: ∀G,L,U1,U2,dt,et. ⦃G, L⦄ ⊢ U1 ▶*[dt, et] U2 →
                   ∀T1,d,e. ⇧[d, e] T1 ≡ U1 →
                   d ≤ dt → d + e ≤ dt + et →
                   ∃∃T2. ⦃G, L⦄ ⊢ U1 ▶*[d+e, dt+et-(d+e)] U2 & ⇧[d, e] T2 ≡ U2.
#G #L #U1 #U2 #dt #et #H #T1 #d #e #HTU1 #Hddt #Hdedet @(cpys_ind … H) -U2
[ /2 width=3 by ex2_intro/
| -HTU1 #U #U2 #_ #HU2 * #T #HU1 #HTU
  elim (cpy_fwd_up … HU2 … HTU) -HU2 -HTU /3 width=3 by cpys_strap1, ex2_intro/
]
qed-.

lemma cpys_fwd_tw: ∀G,L,T1,T2,d,e. ⦃G, L⦄ ⊢ T1 ▶*[d, e] T2 → ♯{T1} ≤ ♯{T2}.
#G #L #T1 #T2 #d #e #H @(cpys_ind … H) -T2 //
#T #T2 #_ #HT2 #IHT1 lapply (cpy_fwd_tw … HT2) -HT2
/2 width=3 by transitive_le/
qed-.

(* Basic inversion lemmas ***************************************************)

(* Note: this can be derived from cpys_inv_atom1 *)
lemma cpys_inv_sort1: ∀G,L,T2,k,d,e. ⦃G, L⦄ ⊢ ⋆k ▶*[d, e] T2 → T2 = ⋆k.
#G #L #T2 #k #d #e #H @(cpys_ind … H) -T2 //
#T #T2 #_ #HT2 #IHT1 destruct
>(cpy_inv_sort1 … HT2) -HT2 //
qed-.

(* Note: this can be derived from cpys_inv_atom1 *)
lemma cpys_inv_gref1: ∀G,L,T2,p,d,e. ⦃G, L⦄ ⊢ §p ▶*[d, e] T2 → T2 = §p.
#G #L #T2 #p #d #e #H @(cpys_ind … H) -T2 //
#T #T2 #_ #HT2 #IHT1 destruct
>(cpy_inv_gref1 … HT2) -HT2 //
qed-.

lemma cpys_inv_bind1: ∀a,I,G,L,V1,T1,U2,d,e. ⦃G, L⦄ ⊢ ⓑ{a,I}V1.T1 ▶*[d, e] U2 →
                      ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ▶*[d, e] V2 &
                               ⦃G, L.ⓑ{I}V1⦄ ⊢ T1 ▶*[⫯d, e] T2 &
                               U2 = ⓑ{a,I}V2.T2.
#a #I #G #L #V1 #T1 #U2 #d #e #H @(cpys_ind … H) -U2
[ /2 width=5 by ex3_2_intro/
| #U #U2 #_ #HU2 * #V #T #HV1 #HT1 #H destruct
  elim (cpy_inv_bind1 … HU2) -HU2 #V2 #T2 #HV2 #HT2 #H
  lapply (lsuby_cpy_trans … HT2 (L.ⓑ{I}V1) ?) -HT2
  /3 width=5 by cpys_strap1, lsuby_succ, ex3_2_intro/
]
qed-.

lemma cpys_inv_flat1: ∀I,G,L,V1,T1,U2,d,e. ⦃G, L⦄ ⊢ ⓕ{I}V1.T1 ▶*[d, e] U2 →
                      ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ▶*[d, e] V2 & ⦃G, L⦄ ⊢ T1 ▶*[d, e] T2 &
                               U2 = ⓕ{I}V2.T2.
#I #G #L #V1 #T1 #U2 #d #e #H @(cpys_ind … H) -U2
[ /2 width=5 by ex3_2_intro/
| #U #U2 #_ #HU2 * #V #T #HV1 #HT1 #H destruct
  elim (cpy_inv_flat1 … HU2) -HU2
  /3 width=5 by cpys_strap1, ex3_2_intro/
]
qed-.

lemma cpys_inv_refl_O2: ∀G,L,T1,T2,d. ⦃G, L⦄ ⊢ T1 ▶*[d, 0] T2 → T1 = T2.
#G #L #T1 #T2 #d #H @(cpys_ind … H) -T2 //
#T #T2 #_ #HT2 #IHT1 <(cpy_inv_refl_O2 … HT2) -HT2 //
qed-.

lemma cpys_inv_lift1_eq: ∀G,L,U1,U2. ∀d,e:nat.
                         ⦃G, L⦄ ⊢ U1 ▶*[d, e] U2 → ∀T1. ⇧[d, e] T1 ≡ U1 → U1 = U2.
#G #L #U1 #U2 #d #e #H #T1 #HTU1 @(cpys_ind … H) -U2
/2 width=7 by cpy_inv_lift1_eq/
qed-.
