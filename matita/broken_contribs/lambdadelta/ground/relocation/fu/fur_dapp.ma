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
include "ground/relocation/fu/ur_dapp.ma".

(* DEPTH APPLICATION FOR FINITE RELOCATION MAPS FOR UNWIND ******************)

rec definition fur_dapp (f) on f: ℕ⁺ → ℕ⁺ ≝
match f with
[ list_empty     ⇒ λp.p
| list_lcons i g ⇒ i＠⧣❨fur_dapp g❩
].

interpretation
  "depth application (finite relocation maps for unwind)"
  'AtSharp f p = (fur_dapp f p).

(* Basic constructions ******************************************************)

lemma fur_dapp_id (p):
      p = 𝐢＠⧣❨p❩.
// qed.

lemma fur_dapp_p_dx_unit (f):
      (𝟏) = (⫯f)＠⧣❨𝟏❩.
// qed.

lemma fur_dapp_p_dx_succ (f) (p):
      ↑(f＠⧣❨p❩) = (⫯f)＠⧣❨↑p❩.
// qed.

lemma fur_dapp_j_dx (f) (n) (p):
      f＠⧣❨p+n❩ = (⮤*[n]f)＠⧣❨p❩.
// qed.
