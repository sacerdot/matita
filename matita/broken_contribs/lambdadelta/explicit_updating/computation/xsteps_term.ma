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

include "explicit_updating/reduction/xstep_term.ma".
include "explicit_updating/notation/relations/black_rightarrow_star_3.ma".

(* X-COMPUTATION FOR TERM ***************************************************)

inductive xsteps_term (R:relation2 …) (t1): predicate … ≝
| xsteps_term_refl (t2):
  t1 ≐ t2 → xsteps_term R t1 t2
| xsteps_term_dx (t) (t2):
  xsteps_term R t1 t → t ➡[R] t2 → xsteps_term R t1 t2
.

interpretation
  "x-computation (term)"
  'BlackRightArrowStar t1 R t2 = (xsteps_term R t1 t2).

(* Advanced constructions ***************************************************)

lemma xsteps_term_subeq (R1) (R2):
      R1 ⊆ R2 → (xsteps_term R1) ⊆ (xsteps_term R2).
#R1 #R2 #HR #t1 #t2 #Ht elim Ht -t2
/3 width=5 by xstep_term_subeq, xsteps_term_refl, xsteps_term_dx/
qed.

lemma xsteps_term_abst_bi (R) (b) (t1) (t2):
      t1 ➡*[R] t2 → 𝛌b.t1 ➡*[R] 𝛌b.t2.
#R #b #t1 #t2 #Ht12 elim Ht12 -t2
[ /3 width=1 by term_eq_abst, xsteps_term_refl/
| /3 width=3 by xstep_term_abst, xsteps_term_dx/
]
qed.

lemma xsteps_term_appl_bi (R) (v1) (v2) (t1) (t2):
      v1 ➡*[R] v2 → t1 ➡*[R] t2 → ＠v1.t1 ➡*[R] ＠v2.t2.
#R #v1 #v2 #t1 #t2 #Hv12 elim Hv12 -v2
[ #v2 #Hv12 #Ht12 elim Ht12 -t2
  [ /3 width=1 by term_eq_appl, xsteps_term_refl/
  | /3 width=5 by xstep_term_head, xsteps_term_dx/
  ]
| /3 width=5 by xstep_term_side, xsteps_term_dx/
]
qed. 

lemma xsteps_term_lift_bi (R) (f1) (f2) (t1) (t2):
      f1 ≐ f2 → t1 ➡*[R] t2 → 𝛗f1.t1 ➡*[R] 𝛗f2.t2.
#R #f1 #f2 #t1 #t2 #Hf12 #Ht12 elim Ht12 -t2
[ /3 width=1 by term_eq_lift, xsteps_term_refl/
| /3 width=5 by xstep_term_lift, xsteps_term_dx/
]
qed.

(* Constructions with term_eq ***********************************************)

lemma xsteps_term_eq_repl (R):
      replace_2 … term_eq term_eq R →
      replace_2 … term_eq term_eq (xsteps_term R).
#R #HR #t1 #t2 #H0 elim H0 -t2
[ /3 width=5 by xsteps_term_refl, term_eq_repl/
| /3 width=5 by xsteps_term_dx, xstep_term_eq_trans/
]
qed-.

lemma xsteps_term_eq_trans (R) (t) (t1) (t2):
      replace_2 … term_eq term_eq R →
      t1 ➡*[R] t → t ≐ t2 → t1 ➡*[R] t2.
/2 width=5 by xsteps_term_eq_repl/
qed-.

lemma eq_xsteps_term_trans (R) (t) (t1) (t2):
      replace_2 … term_eq term_eq R →
      t1 ≐ t → t ➡*[R] t2 → t1 ➡*[R] t2.
/3 width=5 by xsteps_term_eq_repl, term_eq_sym/
qed-.

(* Basic constructions ******************************************************)

lemma xsteps_term_step (R) (t1) (t2):
      t1 ➡[R] t2 → t1 ➡*[R] t2.
/3 width=3 by xsteps_term_refl, xsteps_term_dx/
qed.

(* Main constructions *******************************************************)

theorem xsteps_term_trans (R):
        replace_2 … term_eq term_eq R →
        Transitive … (xsteps_term R).
#R #HR #t1 #t #Ht1 #t2 #Ht2 elim Ht2 -t2
[ /2 width=3 by xsteps_term_eq_trans/
| /2 width=3 by xsteps_term_dx/
]
qed-.
