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

include "ground/relocation/pr_isd.ma".
include "ground/relocation/pr_sle.ma".

(* INCLUSION FOR PARTIAL RELOCATION MAPS ************************************)

(* Constructions with pr_isd ************************************************)

(*** sle_isdiv_dx *)
corec lemma pr_sle_isd_dx:
            ∀f2. 𝛀❨f2❩ → ∀f1. f1 ⊆ f2.
#f2 * -f2
#f2 #g2 #Hf2 #H2 #f1 cases (pr_map_split_tl f1) *
/3 width=5 by pr_sle_weak, pr_sle_next/
qed.

(* Inversions with pr_isd ***************************************************)

(*** sle_inv_isdiv_sn *)
corec lemma pr_sle_inv_isd_sn:
            ∀f1,f2. f1 ⊆ f2 → 𝛀❨f1❩ → 𝛀❨f2❩.
#f1 #f2 * -f1 -f2
#f1 #f2 #g1 #g2 #Hf * * #H
[1,3: elim (pr_isd_inv_push … H) // ]
lapply (pr_isd_inv_next … H ??) -H
/3 width=3 by pr_isd_next/
qed-.
