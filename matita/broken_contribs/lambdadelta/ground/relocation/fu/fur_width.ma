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
include "ground/notation/functions/updownarrow_1.ma".

(* WIDTH FOR FINITE RELOCATION MAPS FOR UNWIND ******************************)

rec definition fur_width (f) on f: ℕ ≝
match f with
[ list_empty     ⇒ 𝟎
| list_lcons i g ⇒
  match i with
  [ ur_p   ⇒ fur_width g
  | ur_j k ⇒ fur_width g + k
  ]
].

interpretation
  "width (finite relocation maps for unwind)"
  'UpDownArrow f = (fur_width f).

(* Basic constructions ******************************************************)

lemma fur_width_empty: 𝟎 = ↕𝐢.
// qed.

lemma fur_width_p_dx (f):
      (↕f) = ↕(f◖𝗽).
// qed.

lemma fur_width_j_dx (f) (k):
      (↕f)+k = ↕(f◖𝗷k).
// qed.

(* Main constructions *******************************************************)

theorem fur_width_append (f) (g):
        (↕f+↕g) = ↕(f●g).
#f #g elim g -g //
* [| #k ] #g #IH <list_append_lcons_sn
[ <fur_width_p_dx <fur_width_p_dx //
| <fur_width_j_dx <fur_width_j_dx //
]
qed.

(* Constructions with fur_lcons *********************************************)

lemma fur_width_p_sn (f):
      ↕f = ↕(𝗽◗f).
// qed.

lemma fur_width_j_sn (f) (k):
      k+↕f = ↕(𝗷k◗f).
// qed.
