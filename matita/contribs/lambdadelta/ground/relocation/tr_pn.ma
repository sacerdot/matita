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

include "ground/relocation/tr_map.ma".

(* PUSH AND NEXT FOR TOTAL RELOCATION MAPS **********************************)

definition tr_push: tr_map → tr_map ≝
           λf. 𝟏⨮f.

interpretation
  "push (total relocation maps)"
  'UpSpoon f = (tr_push f).

definition tr_next: tr_map → tr_map.
* #p #f @(↑p⨮f)
defined.

interpretation
  "next (total relocation maps)"
  'UpArrow f = (tr_next f).

(* Basic constructions ******************************************************)

lemma tr_push_unfold (f): 𝟏⨮f = ⫯f.
// qed.

lemma tr_next_unfold (f): ∀p. (↑p)⨮f = ↑(p⨮f).
// qed.

(* Constructions with tr_inj ************************************************)

lemma tr_inj_push (f): ⫯𝐭❨f❩ = 𝐭❨⫯f❩.
// qed.

lemma tr_inj_next (f): ↑𝐭❨f❩ = 𝐭❨↑f❩.
* //
qed.
