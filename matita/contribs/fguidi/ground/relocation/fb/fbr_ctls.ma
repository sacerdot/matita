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

include "ground/relocation/fb/fbr_ctl.ma".
include "ground/arith/nat_succ_iter.ma".
include "ground/notation/functions/downspoonstar_2.ma".

(* ITERATED COARSE TAIL FOR FINITE RELOCATION MAPS WITH BOOLEANS ************)

definition fbr_ctls (n:ℕ): 𝔽𝔹 → 𝔽𝔹 ≝
           (λf.⫰f)^n.

interpretation
  "iterated coarse tail (finite relocation maps with booleans)"
  'DownSpoonStar n f = (fbr_ctls n f).

(* Basic constructions ******************************************************)

lemma fbr_ctls_zero (f):
      f = ⫰*[𝟎]f.
// qed.

lemma fbr_ctls_unit (f):
      (⫰f) = ⫰*[⁤𝟏]f.
// qed-.

lemma fbr_ctls_ctl (n) (f):
      (⫰⫰*[n]f) = ⫰*[n]⫰f.
#n #f @(niter_appl … (λf.⫰f))
qed.

lemma fbr_ctls_pos (p) (f):
      (⫰⫰*[↓p]f) = ⫰*[⁤p]f.
#n #f @(niter_pos_ppred … (λf.⫰f))
qed.

lemma fbr_ctls_succ (n) (f):
      (⫰⫰*[n]f) = ⫰*[⁤↑n]f.
#n #f @(niter_succ … (λf.⫰f))
qed.

lemma fbr_ctls_pos_swap (p) (f):
      (⫰*[↓p]⫰f) = ⫰*[⁤p]f.
// qed.

lemma fbr_ctls_succ_swap (n) (f):
      (⫰*[n]⫰f) = ⫰*[⁤↑n]f.
// qed.

(* Advanced constructions ***************************************************)

lemma fbr_ctls_id (n):
      (𝐢) = ⫰*[n]𝐢.
#n @(nat_ind_succ … n) -n //
#n #IH
<fbr_ctls_succ_swap //
qed.

lemma fbr_ctls_pos_push (f) (p):
      (⫰*[↓p]f) = ⫰*[⁤p]⫯f.
// qed.

lemma fbr_ctls_succ_push (f) (n):
      (⫰*[n]f) = ⫰*[⁤↑n]⫯f.
// qed.

lemma fbr_ctls_pos_next (f) (p):
      (⫰*[⁤p]f) = ⫰*[⁤p]↑f.
// qed.
