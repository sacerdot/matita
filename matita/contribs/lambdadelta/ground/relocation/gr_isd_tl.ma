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

include "ground/relocation/gr_tl.ma".
include "ground/relocation/gr_isd.ma".

(* DIVERGENCE CONDITION FOR GENERIC RELOCATION MAPS ***********************************************************)

(* Properties with tail *****************************************************)

(*** isdiv_tl *)
lemma gr_isd_tl (f): 𝛀❪f❫ → 𝛀❪⫱f❫.
#f cases (gr_map_split_tl f) * #H
[ elim (gr_isd_inv_push … H) -H //
| /2 width=3 by gr_isd_inv_next/
]
qed.
