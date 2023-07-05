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
include "ground/relocation/t1/tr_pn.ma".

(* ITERATED PUSH FOR TOTAL RELOCATION MAPS **********************************)

definition tr_pushs (f:tr_map) (n:ℕ) ≝
           (tr_push^n) f.

interpretation
  "iterated push (total relocation maps)"
  'UpSpoonStar n f = (tr_pushs f n).

(* Basic constructions ******************************************************)

lemma tr_pushs_zero:
      ∀f. f = ⫯*[𝟎] f.
// qed.

lemma tr_pushs_push (n):
      ∀f. ⫯⫯*[n] f = ⫯*[n] ⫯f.
#n #f @(niter_appl … tr_push)
qed.

lemma tr_pushs_succ (n):
      ∀f. ⫯⫯*[n] f = ⫯*[⁤↑n] f.
#f #n @(niter_succ … tr_push)
qed.

lemma tr_pushs_swap (n):
      ∀f. ⫯*[n] ⫯f = ⫯*[⁤↑n] f.
// qed.
