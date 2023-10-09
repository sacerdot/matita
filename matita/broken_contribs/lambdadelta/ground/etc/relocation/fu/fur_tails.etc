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
include "ground/notation/functions/downspoonstar_2.ma".

(* ITERATED TAIL FOR FINITE RELOCATION MAPS FOR UNWIND **********************)

rec definition fur_tails (n) (f) on f: 𝔽𝕌 ≝
match n with
[ nzero  ⇒ f
| npos p ⇒ 
  match f with
  [ list_empty     ⇒ f
  | list_lcons i g ⇒
    match i with
    [ ur_p   ⇒ fur_tails (↓p) g
    | ur_j k ⇒ fur_tails (n+k) g
    ]
  ]
].

interpretation
  "iterated tail (finite relocation maps for unwind)"
  'DownSpoonStar n f = (fur_tails n f).

(* Basic constructions ******************************************************)

lemma fur_tails_zero (f):
      f = ⫰*[𝟎]f.
* // qed.

lemma fur_tails_id (n):
      (𝐢) = ⫰*[n]𝐢.
* // qed.

lemma fur_tails_pos_p_dx (f) (p):
      (⫰*[↓p]f) = ⫰*[⁤p]⫯f.
// qed.

lemma fur_tails_succ_p_dx (f) (n):
      (⫰*[n]f) = ⫰*[⁤↑n]⫯f.
// qed.

lemma fur_tails_pos_j_dx (f) (p) (k):
      (⫰*[(⁤p)+k]f) = ⫰*[⁤p]⮤*[k]f.
// qed.
(*
lemma fur_tails_succ_j_dx (f) (n) (k):
      (⫰*[⁤↑(n+k)]f) = ⫰*[⁤↑n]⮤*[k]f.
// qed.
*)