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
include "ground/relocation/gr_map.ma".

(* ITERATED PUSH FOR GENERIC RELOCATION MAPS ********************************)

(*** pushs *)
definition gr_pushs (f:gr_map) (n:nat) ≝
           (gr_push^n) f.

interpretation
  "iterated push (generic relocation maps)"
  'UpSpoonStar n f = (gr_pushs f n).

(* Basic constructions ******************************************************)

(*** pushs_O *)
lemma gr_pushs_zero:
      ∀f. f = ⫯*[𝟎] f.
// qed.

(*** push_swap *)
lemma gr_pushs_push (n):
      ∀f. ⫯⫯*[n] f = ⫯*[n] ⫯f.
#n #f @(niter_appl … gr_push)
qed.

(*** pushs_S *)
lemma gr_pushs_succ (n):
      ∀f. ⫯⫯*[n] f = ⫯*[↑n] f.
#f #n @(niter_succ … gr_push)
qed.

(*** pushs_xn *)
lemma gr_pushs_swap (n):
      ∀f. ⫯*[n] ⫯f = ⫯*[↑n] f.
// qed.
