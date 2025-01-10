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

include "explicit_updating/syntax/term_valid.ma".
include "explicit_updating/reduction/xbeta1.ma".
include "explicit_updating/computation/xsteps_term.ma".
include "explicit_updating/notation/relations/black_rightarrow_star_2.ma".

(* X-COMPUTATION TO ♭-NORMAL FORM FOR TERM **********************************)

definition xsteps_phi: relation2 … ≝
           λt1,t2. ∧∧ t1 ➡*[𝛃ⓣ] t2 & ⓕ ⊢ t2.

interpretation
  "x-computation to ♭-normal form (term)"
  'BlackRightArrowStar t1 t2 = (xsteps_phi t1 t2).

(* Basic constructions ******************************************************)

lemma xsteps_phi_fold (t1) (t2):
      t1 ➡*[𝛃ⓣ] t2 → ⓕ ⊢ t2 → t1 ➡*𝛟 t2.
/2 width=1 by conj/
qed.
