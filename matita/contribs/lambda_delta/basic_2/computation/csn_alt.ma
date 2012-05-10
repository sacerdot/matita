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

include "basic_2/computation/cprs.ma".
include "basic_2/computation/csn.ma".

(* CONTEXT-SENSITIVE STRONGLY NORMALIZING TERMS *****************************)

(* alternative definition of csn *)
definition csna: lenv → predicate term ≝ λL. SN … (cprs L) (eq …).

interpretation
   "context-sensitive strong normalization (term) alternative"
   'SNAlt L T = (csna L T).

(* Basic eliminators ********************************************************)

lemma csna_ind: ∀L. ∀R:predicate term.
                (∀T1. L ⊢ ⬇⬇* T1 →
                      (∀T2. L ⊢ T1 ➡* T2 → (T1 = T2 → False) → R T2) → R T1
                ) →
                ∀T. L ⊢ ⬇⬇* T → R T.
#L #R #H0 #T1 #H elim H -T1 #T1 #HT1 #IHT1
@H0 -H0 /3 width=1/ -IHT1 /4 width=1/
qed-.

(* Basic properties *********************************************************)

(* Basic_1: was: sn3_intro *)
lemma csna_intro: ∀L,T1.
                  (∀T2. L ⊢ T1 ➡* T2 → (T1 = T2 → False) → L ⊢ ⬇⬇* T2) → L ⊢ ⬇⬇* T1.
#L #T1 #H
@(SN_intro … H)
qed.

fact csna_intro_aux: ∀L,T1.
                     (∀T,T2. L ⊢ T ➡* T2 → T1 = T → (T1 = T2 → False) → L ⊢ ⬇⬇* T2) → L ⊢ ⬇⬇* T1.
/4 width=3/ qed-.

(* Basic_1: was: sn3_pr3_trans (old version) *)
lemma csna_cprs_trans: ∀L,T1. L ⊢ ⬇⬇* T1 → ∀T2. L ⊢ T1 ➡* T2 → L ⊢ ⬇⬇* T2.
#L #T1 #H elim H -T1 #T1 #HT1 #IHT1 #T2 #HLT12
@csna_intro #T #HLT2 #HT2
elim (term_eq_dec T1 T2) #HT12
[ -IHT1 -HLT12 destruct /3 width=1/
| -HT1 -HT2 /3 width=4/
qed.

(* Basic_1: was: sn3_pr2_intro (old version) *)
lemma csna_intro_cpr: ∀L,T1.
                      (∀T2. L ⊢ T1 ➡ T2 → (T1 = T2 → False) → L ⊢ ⬇⬇* T2) →
                      L ⊢ ⬇⬇* T1.
#L #T1 #H
@csna_intro_aux #T #T2 #H @(cprs_ind_dx … H) -T
[ -H #H destruct #H
  elim (H ?) //
| #T0 #T #HLT1 #HLT2 #IHT #HT10 #HT12 destruct
  elim (term_eq_dec T0 T) #HT0
  [ -HLT1 -HLT2 -H /3 width=1/
  | -IHT -HT12 /4 width=3/
  ]
] 
qed.

(* Main properties **********************************************************)

theorem csn_csna: ∀L,T. L ⊢ ⬇* T → L ⊢ ⬇⬇* T.
#L #T #H @(csn_ind … H) -T /4 width=1/
qed.

theorem csna_csn: ∀L,T. L ⊢ ⬇⬇* T → L ⊢ ⬇* T.
#L #T #H @(csna_ind … H) -T /4 width=1/
qed.

(* Basic_1: was: sn3_pr3_trans *)
lemma csn_cprs_trans: ∀L,T1. L ⊢ ⬇* T1 → ∀T2. L ⊢ T1 ➡* T2 → L ⊢ ⬇* T2.
/4 width=3/ qed.

(* Main eliminators *********************************************************)

lemma csn_ind_alt: ∀L. ∀R:predicate term.
                   (∀T1. L ⊢ ⬇* T1 →
                         (∀T2. L ⊢ T1 ➡* T2 → (T1 = T2 → False) → R T2) → R T1
                   ) →
                   ∀T. L ⊢ ⬇* T → R T.
#L #R #H0 #T1 #H @(csna_ind … (csn_csna … H)) -T1 #T1 #HT1 #IHT1
@H0 -H0 /2 width=1/ -HT1 /3 width=1/
qed-.
