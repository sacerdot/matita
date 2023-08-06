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
include "ground/notation/functions/downspoon_1.ma".

(* COARSE TAIL FOR FINITE RELOCATION MAPS WITH BOOLEANS *********************)

rec definition fbr_ctl (f) on f: 𝔽𝔹 ≝
match f with
[ list_empty     ⇒ f
| list_lcons b g ⇒
  match b with
  [ false ⇒ g
  | true  ⇒ fbr_ctl g
  ]
].

interpretation
  "coarse tail (finite relocation maps with booleans)"
  'DownSpoon f = (fbr_ctl f).

(* Basic constructions ******************************************************)

lemma fbr_ctl_id:
      (𝐢) = (⫰𝐢).
// qed.

lemma fbr_ctl_push (f):
      f = (⫰⫯f).
// qed.

lemma fbr_ctl_next (f):
      (⫰f) = (⫰↑f).
// qed.
