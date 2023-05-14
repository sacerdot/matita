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

include "ground/notation/functions/uparrowstar_2.ma".
include "ground/arith/nat_succ_iter.ma".
include "ground/relocation/pr_map.ma".

(* ITERATED NEXT FOR PARTIAL RELOCATION MAPS ********************************)

(*** nexts *)
definition pr_nexts (f:pr_map) (n:ℕ) ≝
           (pr_next^n) f.

interpretation
  "iterated next (partial relocation maps)"
  'UpArrowStar n f = (pr_nexts f n).

(* Basic constructions ******************************************************)

(*** nexts_O *)
lemma pr_nexts_zero:
      ∀f. f = ↑*[𝟎] f.
// qed.

(*** nexts_swap *)
lemma pr_nexts_next (n):
      ∀f. ↑↑*[n] f = ↑*[n] ↑f.
#f #n @(niter_appl … pr_next)
qed.

(*** nexts_S *)
lemma pr_nexts_succ (n):
      ∀f. ↑↑*[n] f = ↑*[↑n] f.
#f #n @(niter_succ … pr_next)
qed.

(*** nexts_xn *)
lemma pr_nexts_swap (n):
      ∀f. ↑*[n] ↑f = ↑*[↑n] f.
// qed.
