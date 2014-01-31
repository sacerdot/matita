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

include "basic_2/reduction/crr_append.ma".
include "basic_2/reduction/cir.ma".

(* IRREDUCIBLE TERMS FOR CONTEXT-SENSITIVE REDUCTION ************************)

(* Advanved properties ******************************************************)

lemma cir_labst_last: ∀G,L,T,W. ⦃G, L⦄ ⊢ ➡ 𝐈⦃T⦄  → ⦃G, ⋆.ⓛW @@ L⦄ ⊢ ➡ 𝐈⦃T⦄.
/3 width=2 by crr_inv_labst_last/ qed.

lemma cir_tif: ∀G,T,W. ⦃G, ⋆⦄ ⊢ ➡ 𝐈⦃T⦄ → ⦃G, ⋆.ⓛW⦄ ⊢ ➡ 𝐈⦃T⦄.
/3 width=2 by crr_inv_trr/ qed.

(* Advanced inversion lemmas ************************************************)

lemma cir_inv_append_sn: ∀G,L,K,T. ⦃G, K @@ L⦄ ⊢ ➡ 𝐈⦃T⦄  → ⦃G, L⦄ ⊢ ➡ 𝐈⦃T⦄.
/3 width=1/ qed-.

lemma cir_inv_tir: ∀G,T,W. ⦃G, ⋆.ⓛW⦄ ⊢ ➡ 𝐈⦃T⦄  → ⦃G, ⋆⦄ ⊢ ➡ 𝐈⦃T⦄.
/3 width=1/ qed-.
