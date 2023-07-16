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

include "ground/relocation/fb/fbr_map.ma".
include "ground/arith/nat_succ_iter.ma".
include "ground/notation/functions/upspoonstar_2.ma".

(* ITERATED PUSH FOR FINITE RELOCATION MAPS WITH BOOLEANS *******************)

definition fbr_pushs (n:ℕ): 𝔽𝔹 → 𝔽𝔹 ≝
           (λf.⫯f)^n.

interpretation
  "iterated push (finite relocation maps with booleans)"
  'UpSpoonStar n f = (fbr_pushs n f).

(* Basic constructions ******************************************************)

lemma fbr_pushs_zero (f):
      f = ⫯*[𝟎] f.
// qed.

lemma fbr_pushs_push (n) (f):
      (⫯⫯*[n]f) = ⫯*[n]⫯f.
#n #f @(niter_appl … (λf.⫯f))
qed.

lemma fbr_pushs_pos (p) (f):
      (⫯⫯*[↓p]f) = ⫯*[⁤p]f.
#n #f @(niter_pos_ppred … (λf.⫯f))
qed.

lemma fbr_pushs_succ (n) (f):
      (⫯⫯*[n]f) = ⫯*[⁤↑n]f.
#n #f @(niter_succ … (λf.⫯f))
qed.

lemma fbr_pushs_swap (n) (f):
      (⫯*[n]⫯f) = ⫯*[⁤↑n]f.
// qed.
