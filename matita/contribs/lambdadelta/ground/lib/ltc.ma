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

include "ground/generated/insert_eq_1.ma".
include "ground/lib/functions.ma".

(* LABELLED TRANSITIVE CLOSURE FOR RELATIONS ********************************)

inductive ltc (A:Type[0]) (f) (B) (R:relation3 A B B): relation3 A B B ≝
| ltc_rc   : ∀a,b1,b2. R a b1 b2 → ltc … a b1 b2
| ltc_trans: ∀a1,a2,b1,b,b2. ltc … a1 b1 b → ltc … a2 b b2 → ltc … (f a1 a2) b1 b2
.

(* Basic constructions ******************************************************)

lemma ltc_sn (A) (f) (B) (R): ∀a1,b1,b. R a1 b1 b →
                              ∀a2,b2. ltc A f B R a2 b b2 → ltc … f … R (f a1 a2) b1 b2.
/3 width=3 by ltc_rc, ltc_trans/ qed.

lemma ltc_dx (A) (f) (B) (R): ∀a1,b1,b. ltc A f B R a1 b1 b →
                              ∀a2,b2. R a2 b b2 → ltc … f … R (f a1 a2) b1 b2.
/3 width=3 by ltc_rc, ltc_trans/ qed.

(* Basic eliminations *******************************************************)

lemma ltc_ind_sn (A) (f) (B) (R) (Q:relation2 A B) (b2): associative … f →
                 (∀a,b1. R a b1 b2 → Q a b1) →
                 (∀a1,a2,b1,b. R a1 b1 b → ltc … f … R a2 b b2 → Q a2 b → Q (f a1 a2) b1) →
                 ∀a,b1. ltc … f … R a b1 b2 → Q a b1.
#A #f #B #R #Q #b2 #Hf #IH1 #IH2 #a #b1 @(insert_eq_1 … b2)
#b0 #H elim H -a -b1 -b0 /2 width=2 by/
#a1 #a2 #b1 #b #b0 #H #Hb2 #_
generalize in match Hb2; generalize in match a2; -Hb2 -a2
elim H -a1 -b1 -b /4 width=4 by ltc_trans/
qed-.

lemma ltc_ind_dx (A) (f) (B) (R) (Q:A→predicate B) (b1): associative … f →
                 (∀a,b2. R a b1 b2 → Q a b2) →
                 (∀a1,a2,b,b2. ltc … f … R a1 b1 b → Q a1 b → R a2 b b2 → Q (f a1 a2) b2) →
                 ∀a,b2. ltc … f … R a b1 b2 → Q a b2.
#A #f #B #R #Q #b1 #Hf #IH1 #IH2 #a #b2 @(insert_eq_1 … b1)
#b0 #H elim H -a -b0 -b2 /2 width=2 by/
#a1 #a2 #b0 #b #b2 #Hb0 #H #IHb0 #_
generalize in match IHb0; generalize in match Hb0; generalize in match a1; -IHb0 -Hb0 -a1
elim H -a2 -b -b2 /4 width=4 by ltc_trans/
qed-.

(* Advanced eliminations (with reflexivity) *********************************)

lemma ltc_ind_sn_refl (A) (i) (f) (B) (R) (Q:relation2 A B) (b2):
                      associative … f → right_identity … f i → reflexive B (R i) →
                      Q i b2 →
                      (∀a1,a2,b1,b. R a1 b1 b → ltc … f … R a2 b b2 → Q a2 b → Q (f a1 a2) b1) →
                      ∀a,b1. ltc … f … R a b1 b2 → Q a b1.
#A #i #f #B #R #Q #b2 #H1f #H2f #HR #IH1 #IH2 #a #b1 #H
@(ltc_ind_sn … R … H1f … IH2 … H) -a -b1 -H1f #a #b1 #Hb12
>(H2f a) -H2f /3 width=4 by ltc_rc/
qed-.

lemma ltc_ind_dx_refl (A) (i) (f) (B) (R) (Q:A→predicate B) (b1):
                      associative … f → left_identity … f i → reflexive B (R i) →
                      Q i b1 →
                      (∀a1,a2,b,b2. ltc … f … R a1 b1 b → Q a1 b → R a2 b b2 → Q (f a1 a2) b2) →
                      ∀a,b2. ltc … f … R a b1 b2 → Q a b2.
#A #i #f #B #R #Q #b1 #H1f #H2f #HR #IH1 #IH2 #a #b2 #H
@(ltc_ind_dx … R … H1f … IH2 … H) -a -b2 -H1f #a #b2 #Hb12
>(H2f a) -H2f /3 width=4 by ltc_rc/
qed-.

(* Constructions with lsub **************************************************)

lemma ltc_lsub_trans: ∀A,f. associative … f →
                      ∀B,C,R,S. (∀n. lsub_trans B C (λL. R L n) S) →
                      ∀n. lsub_trans B C (λL. ltc A f … (R L) n) S.
#A #f #Hf #B #C #R #S #HRS #n #L2 #T1 #T2 #H
@(ltc_ind_dx … Hf ???? H) -n -T2
/3 width=5 by ltc_dx, ltc_rc/
qed-.
