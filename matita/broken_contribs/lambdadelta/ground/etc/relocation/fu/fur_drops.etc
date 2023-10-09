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

include "ground/relocation/fu/fur_map.ma".
include "ground/arith/nat_plus.ma".
include "ground/arith/nat_ppred_psucc.ma".
include "ground/notation/functions/white_downarrowstar_2.ma".

(* ITERATED DROP FOR FINITE RELOCATION MAPS FOR UNWIND **********************)

rec definition fur_drops (n) (f) on f: 𝔽𝕌 ≝
match f with
[ list_empty     ⇒ f
| list_lcons i g ⇒
  match i with
  [ ur_p   ⇒ 
    match n with
    [ nzero  ⇒ f
    | npos p ⇒ fur_drops (↓p) g
    ] 
  | ur_j k ⇒ fur_drops (n+k) g
  ]
].

interpretation
  "iterated drop (finite relocation maps for unwind)"
  'WhiteDownArrowStar n f = (fur_drops n f).

(* Basic constructions ******************************************************)

lemma fur_drops_id (n):
      (𝐢) = ⇩*[n]𝐢.
// qed.

lemma fur_drops_zero_p_dx (f):
      (⫯f) = ⇩*[𝟎]⫯f.
// qed.

lemma fur_drops_pos_p_dx (f) (p):
      (⇩*[↓p]f) = ⇩*[⁤p]⫯f.
// qed.

lemma fur_drops_succ_p_dx (f) (n):
      (⇩*[n]f) = ⇩*[⁤↑n]⫯f.
// qed.

lemma fur_drops_j_dx (f) (n) (k):
      ⇩*[n+k]f = ⇩*[n]⮤*[k]f.
// qed.
