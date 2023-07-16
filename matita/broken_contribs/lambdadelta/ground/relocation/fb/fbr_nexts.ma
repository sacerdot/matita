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
include "ground/notation/functions/uparrowstar_2.ma".

(* ITERATED NEXT FOR FINITE RELOCATION MAPS WITH BOOLEANS *******************)

definition fbr_nexts (n:ℕ): 𝔽𝔹 → 𝔽𝔹 ≝
           (λf.↑f)^n.

interpretation
  "iterated next (finite relocation maps with booleans)"
  'UpArrowStar n f = (fbr_nexts n f).

(* Basic constructions ******************************************************)

lemma fbr_nexts_zero (f):
      f = ↑*[𝟎]f.
// qed.

lemma fbr_nexts_next (n) (f):
      ↑↑*[n]f = ↑*[n]↑f.
#n #f
lapply (niter_appl … (λf:𝔽𝔹.↑f)) #H0 @H0
qed.

lemma fbr_nexts_pos (p) (f):
      ↑↑*[↓p]f = ↑*[⁤p]f.
#n #f
lapply (niter_pos_ppred … (λf:𝔽𝔹.↑f)) #H0 @H0
qed.

lemma fbr_nexts_succ (n) (f):
      ↑↑*[n]f = ↑*[⁤↑n]f.
#n #f
lapply (niter_succ … (λf:𝔽𝔹.↑f)) #H0 @H0
qed.

lemma fbr_nexts_swap (n) (f):
      ↑*[n]↑f = ↑*[⁤↑n]f.
// qed.
