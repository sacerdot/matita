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

include "ground/notation/functions/element_i_0.ma".
include "ground/relocation/tr_pn.ma".

(* IDENTITY ELEMENT FOR TOTAL RELOCATION MAPS *******************************)

corec definition tr_id: tr_map ≝ ⫯tr_id.

interpretation
  "identity element (total relocation maps)"
  'ElementI = (tr_id).

(* Basic constructions ******************************************************)

lemma tr_id_unfold: ⫯𝐢 = 𝐢.
<(stream_unfold … (𝐢)) in ⊢ (???%); //
qed.
