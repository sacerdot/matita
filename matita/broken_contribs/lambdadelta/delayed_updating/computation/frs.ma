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
include "delayed_updating/syntax/prototerm_eq.ma".
include "delayed_updating/computation/trace.ma".

(* FOCALIZED COMPUTATION FOR PROTOTERM **************************************)

inductive frs (R:relation3 (ℙ) (𝕋) (𝕋)): relation3 ( ℙ* ) (𝕋) (𝕋) ≝
| frs_step (t1) (t2) (r):
  R r t1 t2 → frs R (r◗𝐞) t1 t2
| frs_refl (t1) (t2):
  t1 ⇔ t2 → frs R (𝐞) t1 t2
| frs_trans (t) (t1) (t2) (rs) (ss):
  frs R rs t1 t → frs R ss t t2 → frs R (rs●ss) t1 t2
.

(* Advanced constructions ***************************************************)

lemma frs_step_sx (R) (t) (t1) (t2) (ss) (r):
      R r t1 t → frs R ss t t2 → frs R (r◗ss) t1 t2.
#R #t #t1 #t2 #ss #r #Ht1 #Ht2
>(list_append_empty_sx … ss) >list_append_lcons_sx
/3 width=3 by frs_step, frs_trans/
qed.

lemma frs_step_dx (R) (t) (t1) (t2) (rs) (s):
      frs R rs t1 t → R s t t2 → frs R (rs◖s) t1 t2.
/3 width=3 by frs_step, frs_trans/
qed.

(* Basic inversions *********************************************************)

lemma frs_inv_empty (R) (t1) (t2):
      frs R (𝐞) t1 t2 → t1 ⇔ t2.
#R #t1 #t2 @(insert_eq_1 … (𝐞))
#x #H0 elim H0 -t1 -t2 -x [| // ]
[ #t1 #t2 #r #_ #H0 destruct
| #t #t1 #t2 #rs #ss #_ #_ #IH1 #IH2 #H0
  elim (eq_inv_list_empty_append … H0) -H0 #H1 #H2
  /3 width=3 by subset_eq_trans/
]
qed-.

lemma frs_inv_step (R) (t1) (t2) (r):
      (∀t,t1,t2,r. t1 ⇔ t → R r t t2 → R r t1 t2) →
      (∀t,t1,t2,r. R r t1 t → t ⇔ t2 → R r t1 t2) →
      frs R (r◗𝐞) t1 t2 → R r t1 t2.
#R #t1 #t2 #r #H1R #H2R @(insert_eq_1 … (r◗𝐞))
#x #H0 elim H0 -t1 -t2 -x
[ #t1 #t2 #x #Ht #H0 destruct //
| #t1 #t2 #_ #H0 destruct
| #t #t1 #t2 #rs #ss #Ht1 #Ht2 #IH1 #IH2 #H0
  elim (eq_inv_list_lcons_append ????? H0) -H0 *
  [ #H1 #H2 destruct -Ht2 -IH1
    lapply (frs_inv_empty … Ht1) -Ht1 #Ht1
    /3 width=3 by/
  | #xs #H1 #H2 destruct -Ht1 -IH2
    elim (eq_inv_list_empty_append … H2) -H2 #H1 #H2 destruct
    lapply (frs_inv_empty … Ht2) -Ht2 #Ht2
    /3 width=3 by/
  ]
]
qed-.

lemma frs_inv_trans (R) (t1) (t2) (rs) (ss):
      frs R (rs●ss) t1 t2 →
      ∃∃t. frs R rs t1 t & frs R ss t t2.
#R #t1 #t2 #rs #ss
@(insert_eq_1 … (rs●ss)) #xs #H0
generalize in match ss; -ss
generalize in match rs; -rs
elim H0 -t1 -t2 -xs
[ #t1 #t2 #z #Ht #rs #ss #H0
  elim (eq_inv_list_lcons_append ????? (sym_eq … H0)) -H0 *
  [ #H1 #H2 destruct
    /3 width=3 by frs_step, frs_refl, ex2_intro/
  | #zs #H1 #H2 destruct
    elim (eq_inv_list_empty_append … H2) -H2 #H1 #H2 destruct
    /3 width=3 by frs_step, frs_refl, ex2_intro/
  ]
| #t1 #t2 #Ht #rs #ss #H0
  elim (eq_inv_list_append_empty … H0) -H0 #H1 #H2 destruct
  /3 width=3 by frs_refl, ex2_intro/
| #t #t1 #t2 #xs #ys #Ht1 #Ht2 #IH1 #IH2 #rs #ss #H0
  elim (eq_inv_list_append_bi … H0) -H0 * #zs #H1 #H2 destruct
  [ -Ht2 -IH1
    elim (IH2 zs ss) -IH2 // #t0 #Ht #Ht2
    /3 width=3 by frs_trans, ex2_intro/
  | -Ht1 -IH2
    elim (IH1 rs zs) -IH1 // #t0 #Ht #Ht2
    /3 width=5 by frs_trans, ex2_intro/
  ]
]
qed-.

(* Advanced inversions ******************************************************)

lemma frs_inv_step_sx (R) (t1) (t2) (ss) (r):
      (∀t,t1,t2,r. t1 ⇔ t → R r t t2 → R r t1 t2) →
      (∀t,t1,t2,r. R r t1 t → t ⇔ t2 → R r t1 t2) →
      frs R (r◗ss) t1 t2 →
      ∃∃t. R r t1 t & frs R ss t t2.
#R #t1 #t2 #ss #r #H1R #H2R
>(list_append_empty_sx … ss) >list_append_lcons_sx #Ht
elim (frs_inv_trans … Ht) -Ht #t #Ht1 #Ht2
lapply (frs_inv_step … H1R H2R … Ht1) -H1R -H2R -Ht1 #Ht1
/2 width=3 by ex2_intro/
qed-.

lemma frs_inv_step_dx (R) (t1) (t2) (rs) (s):
      (∀t,t1,t2,r. t1 ⇔ t → R r t t2 → R r t1 t2) →
      (∀t,t1,t2,r. R r t1 t → t ⇔ t2 → R r t1 t2) →
      frs R (rs◖s) t1 t2 →
      ∃∃t. frs R rs t1 t & R s t t2.
#R #t1 #t2 #rs #s #H1R #H2R #Ht
elim (frs_inv_trans … Ht) -Ht #t #Ht1 #Ht2
lapply (frs_inv_step … H1R H2R … Ht2) -H1R -H2R -Ht2 #Ht2
/2 width=3 by ex2_intro/
qed-.

(* Advanced eliminators *****************************************************)

lemma frs_ind_sx (R) (t2) (Q:relation2 …):
      (∀t,t1,t2,r. t1 ⇔ t → R r t t2 → R r t1 t2) →
      (∀t,t1,t2,r. R r t1 t → t ⇔ t2 → R r t1 t2) →
      (∀t1,t2,rs. t1 ⇔ t2 → Q t2 rs → Q t1 rs) →
      (Q t2 (𝐞)) →
      (∀t,t1,ss,r. R r t1 t → frs R ss t t2 → Q t ss → Q t1 (r◗ss)) →
      ∀t1,rs. frs R rs t1 t2 → Q t1 rs.
#R #t2 #Q #H1R #H2R #HQ #IH1 #IH2 #t1 #rs
generalize in match t1; -t1
elim rs -rs [| #r #rs #IH ] #t1 #Ht
[ lapply (frs_inv_empty … Ht) -Ht #Ht
  /3 width=3 by/
| elim (frs_inv_step_sx … H1R H2R … Ht) -Ht #t #Ht1 #Ht2
  /3 width=4 by/
]
qed-.

lemma frs_ind_dx (R) (t1) (Q:relation2 …):
      (∀t,t1,t2,r. t1 ⇔ t → R r t t2 → R r t1 t2) →
      (∀t,t1,t2,r. R r t1 t → t ⇔ t2 → R r t1 t2) →
      (∀t1,t2,rs. t1 ⇔ t2 → Q t2 rs → Q t1 rs) →
      (Q t1 (𝐞)) →
      (∀t,t2,rs,s. frs R rs t1 t → R s t t2 → Q t rs → Q t2 (rs◖s)) →
      ∀t2,rs. frs R rs t1 t2 → Q t2 rs.
#R #t1 #Q #H1R #H2R #HQ #IH1 #IH2 #t2 #rs
generalize in match t2; -t2
@(list_ind_rcons … rs) -rs [| #rs #r #IH ] #t2 #Ht
[ lapply (frs_inv_empty … Ht) -Ht #Ht
  /4 width=3 by subset_eq_sym/
| elim (frs_inv_step_dx … H1R H2R … Ht) -Ht #t #Ht1 #Ht2
  /3 width=4 by/
]
qed-.
