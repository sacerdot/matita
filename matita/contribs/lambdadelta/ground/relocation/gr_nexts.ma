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
include "ground/relocation/gr_map.ma".

(* ITERATED NEXT FOR GENERIC RELOCATION MAPS ********************************)

(*** nexts *)
definition gr_nexts (f:gr_map) (n:nat) ≝
           (gr_next^n) f.

interpretation
  "iterated next (generic relocation maps)"
  'UpArrowStar n f = (gr_nexts f n).

(* Basic constructions ******************************************************)

(*** nexts_O *)
lemma gr_nexts_zero:
      ∀f. f = ↑*[𝟎] f.
// qed.

(*** nexts_swap *)
lemma gr_nexts_next (n):
      ∀f. ↑↑*[n] f = ↑*[n] ↑f.
#f #n @(niter_appl … gr_next)
qed.

(*** nexts_S *)
lemma gr_nexts_succ (n):
      ∀f. ↑↑*[n] f = ↑*[↑n] f.
#f #n @(niter_succ … gr_next)
qed.

(*** nexts_xn *)
lemma gr_nexts_swap (n):
      ∀f. ↑*[n] ↑f = ↑*[↑n] f.
// qed.
