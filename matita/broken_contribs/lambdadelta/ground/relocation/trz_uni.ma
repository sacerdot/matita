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
include "ground/arith/int_plus_opp.ma".
include "ground/notation/functions/element_u_1.ma".
include "ground/notation/functions/element_i_0.ma".

(* UNIFORM ELEMENTS FOR TOTAL RELOCATION MAPS WITH INTEGERS *****************)

definition trz_uni (z:ℤ): trz_map ≝ mk_trz_map ….
[ @(λz0.z0+z)
| /2 width=2 by eq_inv_zplus_dx_bi/
]
defined.

interpretation
  "uniform elements (total relocation maps with integers)"
  'ElementU z = (trz_uni z).

interpretation
  "identity element (total relocation maps with integers)"
  'ElementI = (trz_uni zzero).
