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

include "explicit_updating/reduction/xstep.ma".
include "explicit_updating/notation/relations/black_rightarrow_star_3.ma".

(* X-COMPUTATION ************************************************************)

inductive xsteps (R:relation2 …): relation2 … ≝
| xsteps_refl (t1) (t2):
  t1 ≐ t2 → xsteps R t1 t2
| xsteps_step (t1) (t2):
  t1 ➡[R] t2 → xsteps R t1 t2
| xsteps_trans (t) (t1) (t2):
  xsteps R t1 t → xsteps R t t2 → xsteps R t1 t2
.

interpretation
  "x-computation (term)"
  'BlackRightArrowStar t1 R t2 = (xsteps R t1 t2).

(* Constructions with α-equivalence for term ********************************)

lemma xsteps_eq_repl (R):
      replace_2 … term_eq term_eq R →
      replace_2 … term_eq term_eq (xsteps R).
#R #HR #t1 #t2 #H0 elim H0 -t1 -t2
[ /3 width=5 by xsteps_refl, term_eq_repl/
| /3 width=5 by xsteps_step, xstep_eq_repl/
| /3 width=3 by xsteps_trans/
]
qed-.

lemma xsteps_eq_trans (R) (t) (t1) (t2):
      replace_2 … term_eq term_eq R →
      t1 ➡*[R] t → t ≐ t2 → t1 ➡*[R] t2.
/2 width=5 by xsteps_eq_repl/
qed-.

lemma eq_xsteps_trans (R) (t) (t1) (t2):
      replace_2 … term_eq term_eq R →
      t1 ≐ t → t ➡*[R] t2 → t1 ➡*[R] t2.
/3 width=5 by xsteps_eq_repl, term_eq_sym/
qed-.

(* Basic constructions ******************************************************)

lemma xsteps_step_sx (R) (t) (t1) (t2):
      t1 ➡[R] t → t ➡*[R] t2 → t1 ➡*[R] t2.
/3 width=3 by xsteps_step, xsteps_trans/
qed.

lemma xsteps_step_dx (R) (t) (t1) (t2):
      t1 ➡*[R] t → t ➡[R] t2 → t1 ➡*[R] t2.
/3 width=3 by xsteps_step, xsteps_trans/
qed.
