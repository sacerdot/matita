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

include "delayed_updating/notation/functions/subset_sn_0.ma".
include "delayed_updating/reduction/dbfr.ma".

(* STRONG NORMALIZATION FOR PROTOTERM ***************************************)

(* Note: we cannot use the ϵ notation for (tsn t1) and (tsn t2) *)
(*       because the constant subset_in gets in the way         *)
inductive tsn: 𝒫❨𝕋❩ ≝
| tsn_step (t1): (∀t2,r. t1 ➡𝐝𝐛𝐟[r] t2 → (tsn t2)) → (tsn t1)
.

interpretation
  "strong normalization (prototerm)"
  'SubsetSN = (tsn).
