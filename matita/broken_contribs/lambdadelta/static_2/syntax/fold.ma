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

(* FOLD FOR RESTRICTED CLOSURES *********************************************)

rec definition fold L T on L ≝ match L with
[ LAtom     ⇒ T
| LBind L I ⇒ match I with
  [ BUnit _   ⇒ fold L (-ⓛ⋆𝟎.T)
  | BPair I V ⇒ fold L (-ⓑ[I]V.T)
  ]
].

interpretation "fold (restricted closure)" 'plus L T = (fold L T).

(* Basic properties *********************************************************)

lemma fold_atom: ∀T. ⋆ + T = T.
// qed.

lemma fold_unit: ∀I,L,T. L.ⓤ[I]+T = L+(-ⓛ⋆𝟎.T).
// qed.

lemma fold_pair: ∀I,L,V,T. (L.ⓑ[I]V)+T = L+(-ⓑ[I]V.T).
// qed.
