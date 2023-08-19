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

include "ground/relocation/p1/pr_isi.ma".
include "ground/relocation/p1/pr_sle.ma".

(* INCLUSION FOR PARTIAL RELOCATION MAPS ************************************)

(* Constructions with pr_isi ************************************************)

(*** sle_isid_sn *)
corec lemma pr_sle_isi_sn:
            ∀f1. 𝐈❨f1❩ → ∀f2. f1 ⊆ f2.
#f1 * -f1
#f1 #g1 #Hf1 #H1 #f2 cases (pr_map_split_tl f2) *
/3 width=5 by pr_sle_weak, pr_sle_push/
qed.

(* Inversions with pr_isi ***************************************************)

(*** sle_inv_isid_dx *)
corec lemma pr_sle_inv_isi_dx:
            ∀f1,f2. f1 ⊆ f2 → 𝐈❨f2❩ → 𝐈❨f1❩.
#f1 #f2 * -f1 -f2
#f1 #f2 #g1 #g2 #Hf * * #H
[2,3: elim (pr_isi_inv_next … H) // ]
lapply (pr_isi_inv_push … H ??) -H
/3 width=3 by pr_isi_push/
qed-.
