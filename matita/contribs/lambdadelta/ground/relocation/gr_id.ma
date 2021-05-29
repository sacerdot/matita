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
include "ground/relocation/gr_map.ma".

(* IDENTITY ELEMENT FOR GENERIC RELOCATION MAPS *****************************)

(*** id *)
corec definition gr_id: gr_map ≝ ⫯gr_id.

interpretation
  "identity element (generic relocation streams)"
  'ElementI = (gr_id).

(* Basic constructions (specific) *******************************************)

(*** id_rew *)
lemma gr_id_unfold: ⫯𝐢 = 𝐢.
<(stream_unfold … (𝐢)) in ⊢ (???%); //
qed.
