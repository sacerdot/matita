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
include "ground/notation/functions/cocompose_2.ma".

(* CO-COMPOSITION FOR FINITE RELOCATION MAPS WITH BOOLEANS ******************)

rec definition fbr_coafter (f2) (f1) on f2: 𝔽𝔹 ≝
match f2 with
[ list_empty       ⇒ f1
| list_lcons b2 g2 ⇒
  if b2 then
    (⫯(fbr_coafter g2 f1))
  else
    match f1 with
    [ list_empty       ⇒ (𝐢)
    | list_lcons b1 g1 ⇒ (fbr_coafter g2 g1)◖b1
    ]
].

interpretation
  "co-composition (finite relocation maps with booleans)"
  'CoCompose f2 f1 = (fbr_coafter f2 f1).

(* Basic constructions ******************************************************)

lemma fbr_coafter_id_sn (f):
      f = 𝐢~•f.
// qed.

lemma fbr_coafter_push_id (g):
      (𝐢) = (⫯g)~•𝐢.
// qed.

lemma fbr_coafter_push_rcons (g) (f) (b):
      (g~•f)◖b = (⫯g)~•(f◖b).
// qed.

lemma fbr_coafter_next_sn (g) (f):
      (⫯(g~•f)) = (↑g)~•f.
// qed.
