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
include "ground/arith/nat_plus.ma".
include "ground/notation/functions/updownarrow_1.ma".

(* WIDTH FOR FINITE RELOCATION MAPS WITH BOOLEANS ***************************)

rec definition fbr_width (f) on f: ℕ ≝
match f with
[ list_empty     ⇒ 𝟎
| list_lcons i g ⇒
  if i then (⁤↑(fbr_width g)) else fbr_width g
].

interpretation
  "width (finite relocation maps with booleans)"
  'UpDownArrow f = (fbr_width f).

(* Basic constructions ******************************************************)

lemma fbr_width_empty:
      (𝟎) = ↕𝐢.
// qed.

lemma fbr_width_push_dx (f):
      ↕f = ↕⫯f.
// qed.

lemma fbr_width_next_dx (f):
      (⁤↑↕f) = ↕↑f.
// qed.

(* Main constructions *******************************************************)

theorem fbr_width_append (f) (g):
        (↕f+↕g) = ↕(f●g).
#f #g elim g -g //
* #g #IH <list_append_lcons_sn
[ <fbr_width_next_dx <fbr_width_next_dx //
| <fbr_width_push_dx <fbr_width_push_dx //
]
qed.

(* Constructions with fbr_lcons *********************************************)

lemma fbr_width_push_sn (f):
      ↕f = ↕(𝗽◗f).
// qed.

lemma fbr_width_next_sn (f):
      (⁤↑↕f) = ↕(𝗻◗f).
// qed.
