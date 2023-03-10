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

rec definition gw G â match G with
[ GAtom       â ğ
| GPair G I T â gw G + â¯â¨Tâ©
].

interpretation "weight (global environment)" 'Weight G = (gw G).

(* Basic properties *********************************************************)

lemma gw_atom_unfold: ğ = â¯â¨ââ©.
// qed.

lemma gw_pair_unfold (I) (G) (T): â¯â¨Gâ© + â¯â¨Tâ© = â¯â¨G.â[I]Tâ©.
// qed.

lemma gw_pair: âI,G,T. â¯â¨Gâ© < â¯â¨G.â[I]Tâ©.
// qed.
