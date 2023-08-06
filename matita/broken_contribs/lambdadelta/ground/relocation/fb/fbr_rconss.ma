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
include "ground/notation/functions/black_halfcircleleftstar_3.ma".
include "ground/notation/functions/upspoonstar_2.ma".
include "ground/notation/functions/uparrowstar_2.ma".

(* ITERATED RCONS FOR FINITE RELOCATION MAPS WITH BOOLEANS ******************)

definition fbr_rconss (b) (n:ℕ): 𝔽𝔹 → 𝔽𝔹 ≝
           (λf.f◖b)^n.

interpretation
  "iterated rcons (finite relocation maps with booleans)"
  'BlackHalfCircleLeftStar f n b = (fbr_rconss b n f).

interpretation
  "iterated push (finite relocation maps with booleans)"
  'UpSpoonStar n f = (fbr_rconss false n f).

interpretation
  "iterated next (finite relocation maps with booleans)"
  'UpArrowStar n f = (fbr_rconss true n f).

(* Basic constructions ******************************************************)

lemma fbr_rconss_zero (b) (f):
      f = f◖*[𝟎]b.
// qed.

lemma fbr_rconss_unit (b) (f):
      f◖b = f◖*[⁤𝟏]b.
// qed-.

lemma fbr_rconss_rcons (b) (n) (f):
      (f◖*[n]b)◖b = f◖b◖*[n]b.
#b #n #f @(niter_appl … (λf.f◖b))
qed.

lemma fbr_rconss_pos (b) (p) (f):
      (f◖*[↓p]b)◖b = f◖*[⁤p]b.
#b #p #f @(niter_pos_ppred … (λf.f◖b))
qed.

lemma fbr_rconss_succ (b) (n) (f):
      (f◖*[n]b)◖b = f◖*[⁤↑n]b.
#b #n #f @(niter_succ … (λf.f◖b))
qed.

lemma fbr_rconss_pos_swap (b) (p) (f):
      (f◖b)◖*[↓p]b = f◖*[⁤p]b.
// qed.

lemma fbr_rconss_succ_swap (b) (n) (f):
      (f◖b)◖*[n]b = f◖*[⁤↑n]b.
// qed.
