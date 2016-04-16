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

include "basic_2/notation/relations/snalt_5.ma".
include "basic_2/computation/cpxs.ma".
include "basic_2/computation/csx.ma".

(* CONTEXT-SENSITIVE EXTENDED STRONGLY NORMALIZING TERMS ********************)

(* alternative definition of csx *)
definition csxa: ∀h. sd h → relation3 genv lenv term ≝
                 λh,o,G,L. SN … (cpxs h o G L) (eq …).

interpretation
   "context-sensitive extended strong normalization (term) alternative"
   'SNAlt h o G L T = (csxa h o G L T).

(* Basic eliminators ********************************************************)

lemma csxa_ind: ∀h,o,G,L. ∀R:predicate term.
                (∀T1. ⦃G, L⦄ ⊢ ⬊⬊*[h, o] T1 →
                      (∀T2. ⦃G, L⦄ ⊢ T1 ➡*[h, o] T2 → (T1 = T2 → ⊥) → R T2) → R T1
                ) →
                ∀T. ⦃G, L⦄ ⊢ ⬊⬊*[h, o] T → R T.
#h #o #G #L #R #H0 #T1 #H elim H -T1 /5 width=1 by SN_intro/
qed-.

(* Basic properties *********************************************************)

lemma csx_intro_cpxs: ∀h,o,G,L,T1.
                         (∀T2. ⦃G, L⦄ ⊢ T1 ➡*[h, o] T2 → (T1 = T2 → ⊥) → ⦃G, L⦄ ⊢ ⬊*[h, o] T2) →
                      ⦃G, L⦄ ⊢ ⬊*[h, o] T1.
/4 width=1 by cpx_cpxs, csx_intro/ qed.

(* Basic_1: was just: sn3_intro *)
lemma csxa_intro: ∀h,o,G,L,T1.
                  (∀T2. ⦃G, L⦄ ⊢ T1 ➡*[h, o] T2 → (T1 = T2 → ⊥) → ⦃G, L⦄ ⊢ ⬊⬊*[h, o] T2) →
                  ⦃G, L⦄ ⊢ ⬊⬊*[h, o] T1.
/4 width=1 by SN_intro/ qed.

fact csxa_intro_aux: ∀h,o,G,L,T1. (
                        ∀T,T2. ⦃G, L⦄ ⊢ T ➡*[h, o] T2 → T1 = T → (T1 = T2 → ⊥) → ⦃G, L⦄ ⊢ ⬊⬊*[h, o] T2
                     ) → ⦃G, L⦄ ⊢ ⬊⬊*[h, o] T1.
/4 width=3 by csxa_intro/ qed-.

(* Basic_1: was just: sn3_pr3_trans (old version) *)
lemma csxa_cpxs_trans: ∀h,o,G,L,T1. ⦃G, L⦄ ⊢ ⬊⬊*[h, o] T1 →
                       ∀T2. ⦃G, L⦄ ⊢ T1 ➡*[h, o] T2 → ⦃G, L⦄ ⊢ ⬊⬊*[h, o] T2.
#h #o #G #L #T1 #H elim H -T1 #T1 #HT1 #IHT1 #T2 #HLT12
@csxa_intro #T #HLT2 #HT2
elim (eq_term_dec T1 T2) #HT12
[ -IHT1 -HLT12 destruct /3 width=1 by/
| -HT1 -HT2 /3 width=4 by/
qed.

(* Basic_1: was just: sn3_pr2_intro (old version) *)
lemma csxa_intro_cpx: ∀h,o,G,L,T1. (
                         ∀T2. ⦃G, L⦄ ⊢ T1 ➡[h, o] T2 → (T1 = T2 → ⊥) → ⦃G, L⦄ ⊢ ⬊⬊*[h, o] T2
                      ) → ⦃G, L⦄ ⊢ ⬊⬊*[h, o] T1.
#h #o #G #L #T1 #H
@csxa_intro_aux #T #T2 #H @(cpxs_ind_dx … H) -T
[ -H #H destruct #H
  elim H //
| #T0 #T #HLT1 #HLT2 #IHT #HT10 #HT12 destruct
  elim (eq_term_dec T0 T) #HT0
  [ -HLT1 -HLT2 -H /3 width=1 by/
  | -IHT -HT12 /4 width=3 by csxa_cpxs_trans/
  ]
]
qed.

(* Main properties **********************************************************)

theorem csx_csxa: ∀h,o,G,L,T. ⦃G, L⦄ ⊢ ⬊*[h, o] T → ⦃G, L⦄ ⊢ ⬊⬊*[h, o] T.
#h #o #G #L #T #H @(csx_ind … H) -T /4 width=1 by csxa_intro_cpx/
qed.

theorem csxa_csx: ∀h,o,G,L,T. ⦃G, L⦄ ⊢ ⬊⬊*[h, o] T → ⦃G, L⦄ ⊢ ⬊*[h, o] T.
#h #o #G #L #T #H @(csxa_ind … H) -T /4 width=1 by cpx_cpxs, csx_intro/
qed.

(* Basic_1: was just: sn3_pr3_trans *)
lemma csx_cpxs_trans: ∀h,o,G,L,T1. ⦃G, L⦄ ⊢ ⬊*[h, o] T1 →
                      ∀T2. ⦃G, L⦄ ⊢ T1 ➡*[h, o] T2 → ⦃G, L⦄ ⊢ ⬊*[h, o] T2.
#h #o #G #L #T1 #HT1 #T2 #H @(cpxs_ind … H) -T2 /2 width=3 by csx_cpx_trans/
qed-.

(* Main eliminators *********************************************************)

lemma csx_ind_alt: ∀h,o,G,L. ∀R:predicate term.
                   (∀T1. ⦃G, L⦄ ⊢ ⬊*[h, o] T1 →
                         (∀T2. ⦃G, L⦄ ⊢ T1 ➡*[h, o] T2 → (T1 = T2 → ⊥) → R T2) → R T1
                   ) →
                   ∀T. ⦃G, L⦄ ⊢ ⬊*[h, o] T → R T.
#h #o #G #L #R #H0 #T1 #H @(csxa_ind … (csx_csxa … H)) -T1 /4 width=1 by csxa_csx/
qed-.
