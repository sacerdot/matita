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
include "ground/relocation/p1/pr_map.ma".

(* IDENTITY ELEMENT FOR PARTIAL RELOCATION MAPS *****************************)

(*** id *)
corec definition pr_id: pr_map ≝ ⫯pr_id.

interpretation
  "identity element (partial relocation streams)"
  'ElementI = (pr_id).

(* Basic constructions (specific) *******************************************)

(*** id_rew *)
lemma pr_id_unfold: ⫯𝐢 = 𝐢.
<(stream_unfold … (𝐢)) in ⊢ (???%); //
qed.
