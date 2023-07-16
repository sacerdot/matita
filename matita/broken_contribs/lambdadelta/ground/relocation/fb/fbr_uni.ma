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

include "ground/relocation/fb/fbr_nexts.ma".
include "ground/notation/functions/element_u_1.ma".

(* UNIFORM ELEMENTS FOR FINITE RELOCATION MAPS WITH BOOLEANS ****************)

definition fbr_uni (n): 𝔽𝔹 ≝
           ↑*[n]𝐢
.

interpretation
  "uniform elements (finite relocation maps with booleans)"
  'ElementU n = (fbr_uni n).

(* Basic constructions ******************************************************)

lemma fbr_uni_unfold (n):
      ↑*[n]𝐢 = 𝐮❨n❩.
// qed.
