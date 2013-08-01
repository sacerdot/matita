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

include "basic_2/notation/relations/snalt_4.ma".
include "basic_2/computation/cpxs.ma".
include "basic_2/computation/csn.ma".

(* CONTEXT-SENSITIVE EXTENDED STRONGLY NORMALIZING TERMS ********************)

(* alternative definition of csn *)
definition csna: ∀h. sd h → lenv → predicate term ≝
                 λh,g,L. SN … (cpxs h g L) (eq …).

interpretation
   "context-sensitive extended strong normalization (term) alternative"
   'SNAlt h g L T = (csna h g L T).

(* Basic eliminators ********************************************************)

lemma csna_ind: ∀h,g,L. ∀R:predicate term.
                (∀T1. ⦃G, L⦄ ⊢ ⬊⬊*[h, g] T1 →
                      (∀T2. ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2 → (T1 = T2 → ⊥) → R T2) → R T1
                ) →
                ∀T. ⦃G, L⦄ ⊢ ⬊⬊*[h, g] T → R T.
#h #g #L #R #H0 #T1 #H elim H -T1 #T1 #HT1 #IHT1
@H0 -H0 /3 width=1/ -IHT1 /4 width=1/
qed-.

(* Basic properties *********************************************************)

(* Basic_1: was just: sn3_intro *)
lemma csna_intro: ∀h,g,L,T1.
                  (∀T2. ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2 → (T1 = T2 → ⊥) → ⦃G, L⦄ ⊢ ⬊⬊*[h, g] T2) →
                  ⦃G, L⦄ ⊢ ⬊⬊*[h, g] T1.
/4 width=1/ qed.

fact csna_intro_aux: ∀h,g,L,T1. (
                        ∀T,T2. ⦃G, L⦄ ⊢ T ➡*[h, g] T2 → T1 = T → (T1 = T2 → ⊥) → ⦃G, L⦄ ⊢ ⬊⬊*[h, g] T2
                     ) → ⦃G, L⦄ ⊢ ⬊⬊*[h, g] T1.
/4 width=3/ qed-.

(* Basic_1: was just: sn3_pr3_trans (old version) *)
lemma csna_cpxs_trans: ∀h,g,L,T1. ⦃G, L⦄ ⊢ ⬊⬊*[h, g] T1 →
                       ∀T2. ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2 → ⦃G, L⦄ ⊢ ⬊⬊*[h, g] T2.
#h #g #L #T1 #H elim H -T1 #T1 #HT1 #IHT1 #T2 #HLT12
@csna_intro #T #HLT2 #HT2
elim (term_eq_dec T1 T2) #HT12
[ -IHT1 -HLT12 destruct /3 width=1/
| -HT1 -HT2 /3 width=4/
qed.

(* Basic_1: was just: sn3_pr2_intro (old version) *)
lemma csna_intro_cpx: ∀h,g,L,T1. (
                         ∀T2. ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 → (T1 = T2 → ⊥) → ⦃G, L⦄ ⊢ ⬊⬊*[h, g] T2
                      ) → ⦃G, L⦄ ⊢ ⬊⬊*[h, g] T1.
#h #g #L #T1 #H
@csna_intro_aux #T #T2 #H @(cpxs_ind_dx … H) -T
[ -H #H destruct #H
  elim H //
| #T0 #T #HLT1 #HLT2 #IHT #HT10 #HT12 destruct
  elim (term_eq_dec T0 T) #HT0
  [ -HLT1 -HLT2 -H /3 width=1/
  | -IHT -HT12 /4 width=3/
  ]
]
qed.

(* Main properties **********************************************************)

theorem csn_csna: ∀h,g,L,T. ⦃G, L⦄ ⊢ ⬊*[h, g] T → ⦃G, L⦄ ⊢ ⬊⬊*[h, g] T.
#h #g #L #T #H @(csn_ind … H) -T /4 width=1/
qed.

theorem csna_csn: ∀h,g,L,T. ⦃G, L⦄ ⊢ ⬊⬊*[h, g] T → ⦃G, L⦄ ⊢ ⬊*[h, g] T.
#h #g #L #T #H @(csna_ind … H) -T /4 width=1/
qed.

(* Basic_1: was just: sn3_pr3_trans *)
lemma csn_cpxs_trans: ∀h,g,L,T1. ⦃G, L⦄ ⊢ ⬊*[h, g] T1 →
                      ∀T2. ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2 → ⦃G, L⦄ ⊢ ⬊*[h, g] T2.
#h #g #L #T1 #HT1 #T2 #H @(cpxs_ind … H) -T2 // /2 width=3 by csn_cpx_trans/
qed-.

(* Main eliminators *********************************************************)

lemma csn_ind_alt: ∀h,g,L. ∀R:predicate term.
                   (∀T1. ⦃G, L⦄ ⊢ ⬊*[h, g] T1 →
                         (∀T2. ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2 → (T1 = T2 → ⊥) → R T2) → R T1
                   ) →
                   ∀T. ⦃G, L⦄ ⊢ ⬊*[h, g] T → R T.
#h #g #L #R #H0 #T1 #H @(csna_ind … (csn_csna … H)) -T1 #T1 #HT1 #IHT1
@H0 -H0 /2 width=1/ -HT1 /3 width=1/
qed-.
