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

include "explicit_updating/syntax/term_next.ma".

(* ITERATED NEXT FOR TERM ***************************************************)

definition term_nexts (n:ℕ): 𝕋 → 𝕋 ≝
           (λt.↑t)^n.

interpretation
  "iterated next (term)"
  'UpArrowStar n t = (term_nexts n t).

(* Basic constructions ******************************************************)

lemma term_nexts_zero (t):
      t = ↑*[𝟎]t.
// qed.

lemma term_nexts_unit (t):
      ↑t = ↑*[⁤𝟏]t.
// qed-.

lemma term_nexts_next (n) (t):
      ↑↑*[n]t = ↑*[n]↑t.
#n #t @(niter_appl … (λt.↑t))
qed.

lemma term_nexts_pos (p) (t):
      ↑↑*[↓p]t = ↑*[⁤p]t.
#p #t @(niter_pos_ppred … (λt.↑t))
qed.

lemma term_nexts_succ (n) (t:𝕋):
      ↑↑*[n]t = ↑*[⁤↑n]t.
#n #t @(niter_succ … (λt.↑t))
qed.

lemma term_nexts_pos_swap (p) (t):
      ↑*[↓p]↑t = ↑*[⁤p]t.
// qed.

lemma term_nexts_succ_swap (n) (t:𝕋):
      ↑*[n]↑t = ↑*[⁤↑n]t.
// qed.
