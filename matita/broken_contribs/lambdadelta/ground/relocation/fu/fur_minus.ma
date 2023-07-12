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
include "ground/arith/nat_ppred_psucc.ma".

(* RIGHT SUBTRACTION FOR FINITE RELOCATION MAPS FOR UNWIND ******************)

rec definition fur_minus (n) (f) on f: 𝔽𝕌 ≝
match f with
[ list_empty     ⇒ f
| list_lcons i g ⇒
  match i with
  [ ur_p   ⇒ ⫯(fur_minus n g)
  | ur_j k ⇒ 
    match n with
    [ nzero  ⇒ f
    | npos p ⇒ ⮤*[𝟎](fur_minus (↓p) g)
    ]
  ]
].

interpretation
  "right minus (finite relocation maps for unwind)"
  'minus f n = (fur_minus n f).

(* Basic constructions ******************************************************)

lemma fur_minus_id_sn (n):
      (𝐢) = 𝐢-n.
// qed.

lemma fur_minus_push_sn (f) (n):
      (⫯(f-n)) = (⫯f)-n.
// qed.

lemma fur_minus_join_zero (f) (k):
      (⮤*[k]f) = (⮤*[k]f)-𝟎.
// qed.

lemma fur_minus_join_pos (f) (k) (p):
      (⮤*[𝟎](f-↓p)) = (⮤*[k]f)-(⁤p).
// qed.

(* Advanced constructions ***************************************************)

lemma fur_minus_join_succ (f) (k) (n):
      (⮤*[𝟎](f-n)) = (⮤*[k]f)-(⁤↑n).
// qed.

lemma fur_minus_zero_dx (f):
      f = f-𝟎.
#f elim f -f //
* //
qed.

lemma fur_minus_minus_comm (f) (n1) (n2):
      f-n1-n2 = f-n2-n1.
#f elim f -f //
* //
#k #f #IH * //
#p1 * //
#p2 <fur_minus_join_pos <fur_minus_join_pos <IH -IH //
qed.

lemma fur_minus_minus_refl (f) (n):
      f-n = f-n-n.
#f elim f -f //
* //
#k #f #IH * //
#p <fur_minus_join_pos <fur_minus_join_pos <IH -IH //
qed.
