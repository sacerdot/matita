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
include "ground/relocation/fb/br_dapp.ma".

(* DEPTH APPLICATION FOR FINITE RELOCATION MAPS WITH BOOLEANS ***************)

rec definition fbr_dapp (f) on f: ℕ⁺ → ℕ⁺ ≝
match f with
[ list_empty     ⇒ λp.p
| list_lcons b g ⇒ b＠⧣❨fbr_dapp g❩
].

interpretation
  "depth application (finite relocation maps with booleans)"
  'AtSharp f p = (fbr_dapp f p).

(* Basic constructions ******************************************************)

lemma fbr_dapp_id (p):
      p = 𝐢＠⧣❨p❩.
// qed.

lemma fbr_dapp_push_dx_unit (f):
      (𝟏) = (⫯f)＠⧣❨𝟏❩.
// qed.

lemma fbr_dapp_push_dx_succ (f) (p):
      ↑(f＠⧣❨p❩) = (⫯f)＠⧣❨↑p❩.
// qed.

lemma fbr_dapp_next_dx (f) (p):
      ↑(f＠⧣❨p❩) = (↑f)＠⧣❨p❩.
// qed.
