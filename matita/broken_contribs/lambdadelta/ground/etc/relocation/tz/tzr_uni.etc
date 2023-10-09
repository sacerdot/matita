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

include "ground/relocation/tz/tzr_map.ma".
include "ground/arith/int_plus_opp.ma".
include "ground/notation/functions/element_u_1.ma".

(* UNIFORM ELEMENTS FOR TOTAL RELOCATION MAPS WITH INTEGERS *****************)

definition tzr_uni (z:ℤ): tzr_map ≝ mk_tzr_map ….
[ @(λz0.z0+z)
| /2 width=2 by eq_inv_zplus_dx_bi/
]
defined.

interpretation
  "uniform elements (total relocation maps with integers)"
  'ElementU z = (tzr_uni z).

(* Basic constructions ******************************************************)

lemma tzr_uni_dapp (z) (z0):
      z0+z = 𝐮❨z❩＠⧣❨z0❩.
// qed.
