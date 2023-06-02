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

include "ground/relocation/trz_push.ma".
include "ground/arith/nat_succ_iter.ma".
include "ground/notation/functions/upspoonstar_2.ma".

(* ITERATED PUSH FOR TOTAL RELOCATION MAPS WITH INTEGERS ********************)

definition tr_pushs (n:ℕ): trz_map → trz_map ≝
           trz_push^n.

interpretation
  "iterated push (total relocation maps with integers)"
  'UpSpoonStar n f = (tr_pushs n f).

(* Basic constructions ******************************************************)

lemma trz_pushs_zero (f):
      f = ⫯*[𝟎] f.
// qed.

lemma trz_pushs_push (n) (f):
      (⫯⫯*[n]f) = ⫯*[n]⫯f.
#n #f @(niter_appl … trz_push)
qed.

lemma trz_pushs_succ (n) (f):
      (⫯⫯*[n]f) = ⫯*[↑n]f.
#n #f @(niter_succ … trz_push)
qed.

lemma trz_pushs_swap (n) (f):
      (⫯*[n]⫯f) = ⫯*[↑n]f.
// qed.
