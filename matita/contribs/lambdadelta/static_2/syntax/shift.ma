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

include "static_2/syntax/lenv.ma".

(* SHIFT FOR RESTRICTED CLOSURES ********************************************)

rec definition shift L T on L ≝ match L with
[ LAtom     ⇒ T
| LBind L I ⇒ match I with
  [ BUnit _   ⇒ shift L (-ⓛ⋆0.T)
  | BPair I V ⇒ shift L (-ⓑ{I}V.T)
  ]
].

interpretation "shift (restricted closure)" 'plus L T = (shift L T).

(* Basic properties *********************************************************)

lemma shift_atom: ∀T. ⋆ + T = T.
// qed.

lemma shift_unit: ∀I,L,T. L.ⓤ{I}+T = L+(-ⓛ⋆0.T).
// qed.

lemma shift_pair: ∀I,L,V,T. (L.ⓑ{I}V)+T = L+(-ⓑ{I}V.T).
// qed.
