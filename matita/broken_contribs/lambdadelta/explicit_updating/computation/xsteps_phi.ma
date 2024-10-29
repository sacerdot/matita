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

include "explicit_updating/syntax/term_flat_eq.ma".
include "explicit_updating/reduction/xbeta1.ma".
include "explicit_updating/computation/xsteps.ma".
include "explicit_updating/notation/relations/black_rightarrow_star_2.ma".

(* X-COMPUTATION TO ♭-NORMAL FORM *******************************************)

definition xsteps_phi: relation2 … ≝
           λt1,t2. ∧∧ t1 ➡*[𝛃ⓣ] t2 & ♭t2 ≐ t2.

interpretation
  "x-computation to ♭-normal form (term)"
  'BlackRightArrowStar t1 t2 = (xsteps_phi t1 t2).

(* Basic constructions ******************************************************)

lemma xstep_phi_fold (t1) (t2):
      t1 ➡*[𝛃ⓣ] t2 → ♭t2 ≐ t2 → t1 ➡*𝛟 t2.
/2 width=1 by conj/
qed.

(* Constructions with term_eq ***********************************************)

lemma xsteps_phi_eq_repl:
      replace_2 … term_eq term_eq xsteps_phi.
#t1 #t2 * #Ht12 #Ht2 #u1 #Htu1 #u2 #Htu2
lapply (xsteps_eq_repl … Ht12 … Htu1 … Htu2) -t1
[ /2 width=5 by xbeta1_eq_repl/ ] #Hu12
@(xstep_phi_fold … Hu12) -u1
@(term_eq_repl … Ht2) -Ht2 //
@term_flat_eq_repl //
qed-.

lemma xsteps_phi_eq_trans (t) (t1) (t2):
      t1 ➡*𝛟 t → t ≐ t2 → t1 ➡*𝛟 t2.
/2 width=5 by xsteps_phi_eq_repl/
qed-.

lemma eq_xsteps_phi_trans (t) (t1) (t2):
      t1 ≐ t → t ➡*𝛟 t2 → t1 ➡*𝛟 t2.
/3 width=5 by xsteps_phi_eq_repl, term_eq_sym/
qed-.
