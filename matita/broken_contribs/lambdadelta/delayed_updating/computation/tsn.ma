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

inductive tsn: 𝒫❨𝕋❩ ≝
| is_tsn (t1): (∀t2,r. t1 ➡𝐝𝐛𝐟[r] t2 → t2 ϵ tsn) → t1 ϵ tsn
.

interpretation
  "strong normalization (prototerm)"
  'SubsetSN = (tsn).
