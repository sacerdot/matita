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

include "explicit_updating/computation/xsteps.ma".
include "explicit_updating/notation/relations/similarlessthan_4.ma".

(* STRICT ORDER FOR X-COMPUTATION *******************************************)

inductive xlt (R): relation3 … ≝
| xlt_step (t1) (t0) (t2):
  t1 ≐ t0 → t1 ➡[R] t2 → xlt R t1 t0 t2
| xlt_trans_dx (t1) (t0) (t) (t2):
  xlt R t1 t0 t → t ➡*[R] t2 → xlt R t1 t0 t2
| xlt_trans_sn (t1) (t) (t0) (t2):
  t1 ➡[R] t → xlt R t t0 t2 → xlt R t1 t0 t2
.

interpretation
  "strict order (x-computation)"
  'SimilarLessThan t1 R t0 t2 = (xlt R t1 t0 t2).

(* Basic inversions *********************************************************)

lemma xlt_inv_step (R) (t1) (t0) (t2):
      t1 ⪝[R] t0 ⪝ t2 → t1 ➡[R] t2 → t1 ≐ t0.
#R #t1 #t0 #t2 * -t1 -t0 -t2
[ #t1 #t0 #t2 #Ht10 #_ #_ //
| #t1 #t0 #t #t2 #_  


(*
lemma xsteps_inv_step_sx (R) (t1) (t2):
      replace_2 … term_eq term_eq R →
      t1 ➡*[R] t2 →
      ∨∨ t1 ≐ t2
       | ∃∃t. t1 ➡[R] t & t ➡*[R] t2.
#R #t1 #t2 #HR #Ht elim Ht -t1 -t2
[ /2 width=1 by or_introl/
| /4 width=3 by ex2_intro, or_intror, xsteps_refl/
| #t #t1 #t2 #Ht1 #Ht2 #IH1 #IH2
  elim IH1 elim IH2 -IH1 -IH2
  [ -Ht1 -Ht2 #Ht1 #Ht2
    /3 width=3 by term_eq_trans, or_introl/
  | -Ht1 -Ht2 * #u2 #Htu2 #Hut2 #Ht1
    /4 width=3 by eq_xstep_trans, ex2_intro, or_intror/
  | -Ht1 -Ht2 #Ht2 * #u1 #Htu1 #Hu1t
    /4 width=5 by xsteps_eq_trans, ex2_intro, or_intror/
  | -Ht1 #_ * #u1 #Htu1 #Hu1t
    /4 width=5 by ex2_intro, or_intror, xsteps_trans/
  ]
]
qed-.

lemma xsteps_inv_step_dx (R) (t1) (t2):
      replace_2 … term_eq term_eq R →
      t1 ➡*[R] t2 →
      ∨∨ t1 ≐ t2
       | ∃∃t. t1 ➡*[R] t & t ➡[R] t2.
#R #t1 #t2 #HR #Ht elim Ht -t1 -t2
[ /2 width=1 by or_introl/
| /4 width=3 by ex2_intro, or_intror, xsteps_refl/
| #t #t1 #t2 #Ht1 #Ht2 #IH1 #IH2
  elim IH1 elim IH2 -IH1 -IH2
  [ -Ht1 -Ht2 #Ht1 #Ht2
    /3 width=3 by term_eq_trans, or_introl/
  | -Ht1 -Ht2 * #u2 #Htu2 #Hut2 #Ht1
    /4 width=3 by eq_xsteps_trans, ex2_intro, or_intror/
  | -Ht1 -Ht2 #Ht2 * #u1 #Htu1 #Hu1t
    /4 width=5 by xstep_eq_trans, ex2_intro, or_intror/
  | -Ht2 * #u2 #Htu2 #Hut2 #_
    /4 width=5 by ex2_intro, or_intror, xsteps_trans/
  ]
]
qed-.
*)
(* Basic eliminations *******************************************************)

lemma xsteps_ind_dx (R) (Q:relation2 …):
      replace_2 … term_eq term_eq R →
      (∀t1,t2. t1 ≐ t2 → Q t1 t2) →
      (∀t1,t2. (∀t0. t1 ⪝[R] t0 ⪝ t2 → Q t1 t0) → t1 ➡*[R] t2 → Q t1 t2) →
      ∀t1,t2. t1 ➡*[R] t2 → Q t1 t2.
#R #Q #HR #IH1 #IH2 #t1 #t2 #Ht elim Ht -t1 -t2
[ /2 width=1 by/
| #t1 #t2 #Ht
  @IH2 [| /2 width=1 by xsteps_step/ ]
  #t0 #Ht102

lemma xsteps_ind_step_dx (R) (Q:relation …):
      replace_2 … term_eq term_eq R →
      (∀t1,t2. t1 ≐ t2 → Q t1 t2) →
      (∀t1,t,t2. t1 ➡*[R] t → t ➡[R] t2 → Q t1 t → Q t1 t2) →
      ∀t1,t2. t1 ➡*[R] t2 → Q t1 t2.
#R #Q #HR #IH1 #IH2 @(xsteps_ind_sn … HR IH1)
#t1 #t2 #IH #Ht
elim (xsteps_inv_step_dx … HR Ht) -Ht
[ /2 width=1 by/
| * #t #Ht1 #Ht2
  /4 width=7 by xsteps_refl/
]
qed-.
