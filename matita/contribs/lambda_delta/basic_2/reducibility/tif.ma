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

include "basic_2/reducibility/trf.ma".

(* CONTEXT-FREE IRREDUCIBLE TERMS *******************************************)

definition tif: predicate term ≝ λT. 𝐑⦃T⦄ → ⊥.

interpretation "context-free irreducibility (term)"
   'NotReducible T = (tif T).

(* Basic inversion lemmas ***************************************************)

lemma tif_inv_abbr: ∀V,T. 𝐈⦃ⓓV.T⦄ → ⊥.
/2 width=1/ qed-.

lemma tif_inv_abst: ∀V,T. 𝐈⦃ⓛV.T⦄ → 𝐈⦃V⦄ ∧ 𝐈⦃T⦄.
/4 width=1/ qed-.

lemma tif_inv_appl: ∀V,T. 𝐈⦃ⓐV.T⦄ → ∧∧ 𝐈⦃V⦄ & 𝐈⦃T⦄ & 𝐒⦃T⦄.
#V #T #HVT @and3_intro /3 width=1/
generalize in match HVT; -HVT elim T -T //
* // * #U #T #_ #_ #H elim (H ?) -H /2 width=1/
qed-.

lemma tif_inv_cast: ∀V,T. 𝐈⦃ⓣV.T⦄ → ⊥.
/2 width=1/ qed-.

(* Basic properties *********************************************************)

lemma tif_atom: ∀I. 𝐈⦃⓪{I}⦄.
/2 width=4/ qed.

lemma tif_abst: ∀V,T. 𝐈⦃V⦄ →  𝐈⦃T⦄ →  𝐈⦃ⓛV.T⦄.
#V #T #HV #HT #H
elim (trf_inv_abst … H) -H /2 width=1/
qed.

lemma tif_appl: ∀V,T. 𝐈⦃V⦄ →  𝐈⦃T⦄ →  𝐒⦃T⦄ → 𝐈⦃ⓐV.T⦄.
#V #T #HV #HT #S #H
elim (trf_inv_appl … H) -H /2 width=1/
qed.
