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

include "explicit_updating/reduction/xstep_term_valid.ma".
include "explicit_updating/computation/xsteps_term.ma".

(* X-COMPUTATION FOR TERM ***************************************************)

(* Constructions with valid_term ********************************************)

lemma term_valid_xsteps_trans (R) (c):
      (∀b,t1,t2. R (𝛌b.t1) t2 → ⊥) →
      (∀t1,t2. R t1 t2 → c ⊢ t1 → c ⊢ t2) →
      ∀t1. c ⊢ t1 → ∀t2. t1 ➡*[R] t2 → c ⊢ t2.
#R #c #H1R #H2R #t1 #Ht1 #t2 #Ht12 elim Ht12 -t2
[ /2 width=3 by term_valid_eq_repl_fwd/
| #t0 #t2 #_ #Ht02 #Ht0 -t1
  /3 width=6 by term_valid_xstep_trans/
]
qed.

lemma xsteps_term_subeq_valid_false (R1) (R2):
      (∀b,t1,t2. R2 (𝛌b.t1) t2 → ⊥) →
      (∀t1,t2. R2 t1 t2 → ⓕ ⊢ t1 → ⓕ ⊢ t2) →
      (∀t1,t2. ⓕ ⊢ t1 → R1 t1 t2 → R2 t1 t2) →
      ∀t1,t2. ⓕ ⊢ t1 → t1 ➡*[R1] t2 → t1 ➡*[R2] t2.
#R1 #R2 #H1R #H2R #H3R #t1 #t2 #Ht1 #Ht12 elim Ht12 -t2
[ /3 width=5 by xsteps_term_refl, term_eq_repl/
| #t0 #t2 #_ #Ht02 #Ht10
  /5 width=6 by term_valid_xsteps_trans, xsteps_term_dx, xstep_term_subeq_valid_false/
]
qed.
