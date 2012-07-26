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

include "basic_2/reducibility/crf_append.ma".
include "basic_2/reducibility/cif.ma".

(* CONTEXT-SENSITIVE IRREDUCIBLE TERMS **************************************)

(* Advanved properties ******************************************************)

lemma cif_labst_last: ∀L,T,W. L ⊢ 𝐈⦃T⦄  → ⋆.ⓛW @@ L ⊢ 𝐈⦃T⦄.
/3 width=2 by crf_inv_labst_last/ qed.

lemma cif_tif: ∀T,W. ⋆ ⊢ 𝐈⦃T⦄ → ⋆.ⓛW ⊢ 𝐈⦃T⦄.
/3 width=2 by crf_inv_trf/ qed.

(* Advanced inversion lemmas ************************************************)

lemma cif_inv_labst_last: ∀L,T,W. ⋆.ⓛW @@ L ⊢ 𝐈⦃T⦄  → L ⊢ 𝐈⦃T⦄.
/3 width=1/ qed-.

lemma cif_inv_tif: ∀T,W. ⋆.ⓛW ⊢ 𝐈⦃T⦄  → ⋆ ⊢ 𝐈⦃T⦄.
/3 width=1/ qed-.
