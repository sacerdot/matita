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

include "ground/relocation/trz_map.ma".
include "ground/notation/functions/element_i_0.ma".

(* IDENTITY ELEMENT FOR TOTAL RELOCATION MAPS WITH INTEGERS *****************)

definition trz_id: trz_map ≝ mk_trz_map ….
[ @(λz0.z0)
| //
]
defined.

interpretation
  "identity element (total relocation maps with integers)"
  'ElementI = (trz_id).

(* basic constructions ******************************************************)

lemma trz_id_unfold (z0):
      z0 = 𝐢＠⧣❨z0❩.
// qed.
