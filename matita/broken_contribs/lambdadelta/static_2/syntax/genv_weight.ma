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

include "static_2/syntax/term_weight.ma".
include "static_2/syntax/genv.ma".

(* WEIGHT OF A GLOBAL ENVIRONMENT *******************************************)

rec definition gw G ≝ match G with
[ GAtom       ⇒ 𝟏
| GPair G I T ⇒ gw G + ♯❨T❩
].

interpretation "weight (global environment)" 'Weight G = (gw G).

(* Basic properties *********************************************************)

lemma gw_atom_unfold: 𝟏 = ♯❨⋆❩.
// qed.

lemma gw_pair_unfold (I) (G) (T): ♯❨G❩ + ♯❨T❩ = ♯❨G.ⓑ[I]T❩.
// qed.

lemma gw_pair: ∀I,G,T. ♯❨G❩ < ♯❨G.ⓑ[I]T❩.
// qed.
