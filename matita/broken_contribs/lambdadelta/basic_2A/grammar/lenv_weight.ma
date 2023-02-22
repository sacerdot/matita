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

include "basic_2A/grammar/term_weight.ma".
include "basic_2A/grammar/lenv.ma".

(* WEIGHT OF A LOCAL ENVIRONMENT ********************************************)

let rec lw L ≝ match L with
[ LAtom       ⇒ 0
| LPair L _ V ⇒ lw L + ♯{V}
].

interpretation "weight (local environment)" 'Weight L = (lw L).

(* Basic properties *********************************************************)

lemma lw_pair: ∀I,L,V. ♯{L} < ♯{L.ⓑ{I}V}.
/3 width=1 by lt_plus_to_minus_r, monotonic_lt_plus_r/ qed.
