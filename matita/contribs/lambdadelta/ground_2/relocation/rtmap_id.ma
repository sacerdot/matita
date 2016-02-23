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

include "ground_2/relocation/nstream_id.ma".
include "ground_2/relocation/rtmap_isid.ma".

(* RELOCATION MAP ***********************************************************)

(* Basic properties *********************************************************)

lemma id_isid: 𝐈⦃𝐈𝐝⦄.
/3 width=5 by eq_push_isid/ qed.

(* Alternative definition of isid *******************************************)

lemma eq_id_isid: ∀f. 𝐈𝐝 ≗ f → 𝐈⦃f⦄.
/2 width=3 by isid_eq_repl_back/ qed.

lemma eq_id_inv_isid: ∀f. 𝐈⦃f⦄ → 𝐈𝐝 ≗ f.
/2 width=1 by isid_inv_eq_repl/ qed-.
