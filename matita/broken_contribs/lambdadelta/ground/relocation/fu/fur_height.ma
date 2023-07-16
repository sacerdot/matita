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
include "ground/notation/functions/sharp_1.ma".

(* HEIGHT FOR FINITE RELOCATION MAPS FOR UNWIND *****************************)

rec definition fur_height (f) on f: ℕ ≝
match f with
[ list_empty     ⇒ 𝟎
| list_lcons i g ⇒
  match i with
  [ ur_p   ⇒ fur_height g
  | ur_j k ⇒ (⁤↑(fur_height g))
  ]
].

interpretation
  "height (finite relocation maps for unwind)"
  'Sharp f = (fur_height f).

(* Basic constructions ******************************************************)

lemma fur_height_empty: 𝟎 = ♯𝐢.
// qed.

lemma fur_height_p_dx (f):
      (♯f) = ♯(f◖𝗽).
// qed.

lemma fur_height_j_dx (f) (k):
      (⁤↑♯f) = ♯(f◖𝗷k).
// qed.

(* Main constructions *******************************************************)

theorem fur_height_append (f) (g):
        (♯f+♯g) = ♯(f●g).
#f #g elim g -g //
* [| #k ] #g #IH <list_append_lcons_sn
[ <fur_height_p_dx <fur_height_p_dx //
| <fur_height_j_dx <fur_height_j_dx //
]
qed.

(* Constructions with fur_lcons *********************************************)

lemma fur_height_p_sn (f):
      ♯f = ♯(𝗽◗f).
// qed.

lemma fur_height_j_sn (f) (k):
      (⁤↑♯f) = ♯(𝗷k◗f).
// qed.
