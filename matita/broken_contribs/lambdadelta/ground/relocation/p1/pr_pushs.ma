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

include "ground/notation/functions/upspoonstar_2.ma".
include "ground/arith/nat_succ_iter.ma".
include "ground/relocation/p1/pr_map.ma".

(* ITERATED PUSH FOR PARTIAL RELOCATION MAPS ********************************)

(*** pushs *)
definition pr_pushs (f:pr_map) (n:ℕ) ≝
           (pr_push^n) f.

interpretation
  "iterated push (partial relocation maps)"
  'UpSpoonStar n f = (pr_pushs f n).

(* Basic constructions ******************************************************)

(*** pushs_O *)
lemma pr_pushs_zero:
      ∀f. f = ⫯*[𝟎] f.
// qed.

(*** push_swap *)
lemma pr_pushs_push (n):
      ∀f. ⫯⫯*[n] f = ⫯*[n] ⫯f.
#n #f @(niter_appl … pr_push)
qed.

(*** pushs_S *)
lemma pr_pushs_succ (n):
      ∀f. ⫯⫯*[n] f = ⫯*[⁤↑n] f.
#f #n @(niter_succ … pr_push)
qed.

(*** pushs_xn *)
lemma pr_pushs_swap (n):
      ∀f. ⫯*[n] ⫯f = ⫯*[⁤↑n] f.
// qed.
