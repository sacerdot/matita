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

include "basic_2/syntax/term_weight.ma".
include "basic_2/syntax/genv.ma".

(* WEIGHT OF A GLOBAL ENVIRONMENT *******************************************)

rec definition gw G ≝ match G with
[ GAtom       ⇒ 0
| GPair G I T ⇒ gw G + ♯{T}
].

interpretation "weight (global environment)" 'Weight G = (gw G).

(* Basic properties *********************************************************)

lemma gw_pair: ∀I,G,T. ♯{G} < ♯{G.ⓑ{I}T}.
normalize /2 width=1 by monotonic_le_plus_r/ qed.
