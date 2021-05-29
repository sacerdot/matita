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

include "ground/relocation/gr_isd.ma".
include "ground/relocation/gr_sle.ma".

(* INCLUSION FOR GENERIC RELOCATION MAPS ************************************)

(* Constructions with gr_isd ************************************************)

(*** sle_isdiv_dx *)
corec lemma gr_sle_isd_dx:
            ∀f2. 𝛀❪f2❫ → ∀f1. f1 ⊆ f2.
#f2 * -f2
#f2 #g2 #Hf2 #H2 #f1 cases (gr_map_split_tl f1) *
/3 width=5 by gr_sle_weak, gr_sle_next/
qed.

(* Inversions with gr_isd ***************************************************)

(*** sle_inv_isdiv_sn *)
corec lemma gr_sle_inv_isd_sn:
            ∀f1,f2. f1 ⊆ f2 → 𝛀❪f1❫ → 𝛀❪f2❫.
#f1 #f2 * -f1 -f2
#f1 #f2 #g1 #g2 #Hf * * #H
[1,3: elim (gr_isd_inv_push … H) // ]
lapply (gr_isd_inv_next … H ??) -H
/3 width=3 by gr_isd_next/
qed-.
