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
include "ground/arith/nat_psucc.ma".
include "ground/notation/functions/leftrightarrow_1.ma".

(* ITERATED DROP FOR FINITE RELOCATION MAPS WITH BOOLEANS *******************)

rec definition fbr_length (f) on f: ℕ ≝
match f with
[ list_empty     ⇒ (𝟎)
| list_lcons i g ⇒
  match i with
  [ false ⇒
    match fbr_length g with
    [ nzero  ⇒ (𝟎)
    | npos p ⇒ (⁤↑(fbr_length g))
    ]
  | true  ⇒ (⁤↑(fbr_length g))
  ]
].

interpretation
  "length (finite relocation maps with booleans)"
  'LeftRightArrow f = (fbr_length f).

(* Basic constructions ******************************************************)

lemma fbr_length_id:
      (𝟎) = ↔𝐢.
// qed.

lemma fbr_length_push_dx_zero (f):
      (𝟎) = ↔f → (𝟎) = ↔⫯f.
#f #H0 normalize
<H0 -H0 //
qed.

lemma fbr_length_push_dx_pos (f) (p):
      (⁤p) = ↔f → (⁤↑↔f) = ↔⫯f.
#f #p #H0 normalize
<H0 -H0 //
qed.

lemma fbr_length_next_dx (f):
      (⁤↑↔f) = ↔↑f.
// qed.
