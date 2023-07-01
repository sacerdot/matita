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

include "ground/notation/functions/black_circle_2.ma".
include "ground/relocation/f2/fr2_map.ma".

(* CONCATENATION FOR FINITE RELOCATION MAPS WITH PAIRS **********************)

(* Note: this is reverse compose *)
(*** fr2_append *)
rec definition fr2_append f1 f2 on f1 ≝ match f1 with
[ fr2_empty        ⇒ f2
| fr2_lcons d h f1 ⇒ ❨d, h❩◗ fr2_append f1 f2
].

interpretation
  "append (finite relocation maps with pairs)" 
  'BlackCircle f1 f2 = (fr2_append f1 f2).

(* Basic constructions ******************************************************)

(*** mr2_append_nil *)
lemma fr2_append_empty (f2):
      f2 = 𝐞 ● f2.
// qed.

(*** mr2_append_cons *)
lemma fr2_append_lcons (d) (h) (f1) (f2):
      ❨d, h❩◗ (f1 ● f2) = (❨d, h❩◗ f1) ● f2.
// qed.
