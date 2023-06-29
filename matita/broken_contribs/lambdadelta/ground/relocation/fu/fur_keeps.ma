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
include "ground/notation/functions/white_uparrowstar_2.ma".

(* ITERATED KEEP FOR FINITE RELOCATION MAPS FOR UNWIND **********************)

rec definition fur_keeps (n) (f) on f: 𝔽𝕌 ≝
match f with
[ list_empty     ⇒ (𝐢)
| list_lcons i g ⇒
  match i with
  [ ur_p   ⇒ 
    match n with
    [ nzero  ⇒ (𝐢)
    | npos p ⇒ (fur_keeps (↓p) g)◖i
    ]
  | ur_j k ⇒ (fur_keeps (n+k) g)◖i
  ]
].

interpretation
  "iterated keep (finite relocation maps for unwind)"
  'WhiteUpArrowStar n f = (fur_keeps n f).

(* Basic constructions ******************************************************)

lemma fur_keeps_id (n):
      (𝐢) = ⇧*[n]𝐢.
// qed.

lemma fur_keeps_zero_p_dx (f):
      (𝐢) = ⇧*[𝟎]⫯f.
// qed.

lemma fur_keeps_pos_p_dx (f) (p):
      (⫯⇧*[↓p]f) = ⇧*[⁤p]⫯f.
// qed.

lemma fur_keeps_succ_p_dx (f) (n):
      (⫯⇧*[n]f) = ⇧*[⁤↑n]⫯f.
// qed.

lemma fur_keeps_j_dx (f) (n) (k):
      (⮤*[k]⇧*[n+k]f) = ⇧*[n]⮤*[k]f.
// qed.
