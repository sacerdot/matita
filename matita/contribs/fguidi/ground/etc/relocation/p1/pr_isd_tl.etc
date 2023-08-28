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

include "ground/relocation/p1/pr_tl.ma".
include "ground/relocation/p1/pr_isd.ma".

(* DIVERGENCE CONDITION FOR PARTIAL RELOCATION MAPS *************************)

(* Constructions with pr_tl *************************************************)

(*** isdiv_tl *)
lemma pr_isd_tl (f): 𝛀❨f❩ → 𝛀❨⫰f❩.
#f cases (pr_map_split_tl f) * #H
[ elim (pr_isd_inv_push … H) -H //
| /2 width=3 by pr_isd_inv_next/
]
qed.
