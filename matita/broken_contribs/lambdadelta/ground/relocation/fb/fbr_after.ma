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
include "ground/notation/functions/compose_2.ma".

(* COMPOSITION FOR FINITE RELOCATION MAPS WITH BOOLEANS *********************)

rec definition fbr_after (f2) (f1) on f2: 𝔽𝔹 ≝
match f2 with
[ list_empty       ⇒ f1
| list_lcons b2 g2 ⇒
  if b2 then
    ↑(fbr_after g2 f1)
  else
    match f1 with
    [ list_empty       ⇒ f2
    | list_lcons b1 g1 ⇒ (fbr_after g2 g1)◖b1
    ]
].

interpretation
  "composition (finite relocation maps with booleans)"
  'Compose f2 f1 = (fbr_after f2 f1).

(* Basic constructions ******************************************************)

lemma fbr_after_id_sx (f):
      f = 𝐢•f.
// qed.

lemma fbr_after_push_id (g):
      (⫯g) = (⫯g)•𝐢.
// qed.

lemma fbr_after_push_rcons (g) (f) (b):
      (g•f)◖b = (⫯g)•(f◖b).
// qed.

lemma fbr_after_next_sx (g) (f):
      ↑(g•f) = (↑g)•f.
// qed.

(* Advanced constructions ***************************************************)

lemma fbr_after_id_dx (g):
      g = g•𝐢.
#g elim g -g //
* #g #IH //
<fbr_after_next_sx <IH -IH //
qed.

lemma fbr_after_id_comm (g):
      𝐢•g = g•𝐢.
// qed-.

(* Main constructions *******************************************************)

theorem fbr_after_assoc:
        associative … fbr_after.
#f3 elim f3 -f3 //
* #f3 #IH
[ #f2 #f1
  <fbr_after_next_sx <fbr_after_next_sx //
| * // * #f2 * // [|*: #b3 #f3 ]
  <fbr_after_push_rcons
  [ <fbr_after_next_sx <fbr_after_id_dx <fbr_after_id_dx //
  | <fbr_after_next_sx <fbr_after_next_sx <fbr_after_push_rcons //
  | <fbr_after_push_rcons //
  ]
]
qed.
