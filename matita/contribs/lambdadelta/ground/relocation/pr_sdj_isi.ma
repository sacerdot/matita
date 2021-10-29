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

include "ground/relocation/pr_isi.ma".
include "ground/relocation/pr_sdj.ma".

(* DISJOINTNESS FOR PARTIAL RELOCATION MAPS *********************************)

(* Constructions with pr_isi ************************************************)

(*** sdj_isid_dx *)
corec lemma pr_sdj_isi_dx:
            ∀f2. 𝐈❨f2❩ → ∀f1. f1 ∥ f2.
#f2 * -f2
#f2 #g2 #Hf2 #H2 #f1 cases (pr_map_split_tl f1) *
/3 width=5 by pr_sdj_next_push, pr_sdj_push_bi/
qed.

(*** sdj_isid_sn *)
corec lemma pr_sdj_isi_sn:
            ∀f1. 𝐈❨f1❩ → ∀f2. f1 ∥ f2.
#f1 * -f1
#f1 #g1 #Hf1 #H1 #f2 cases (pr_map_split_tl f2) *
/3 width=5 by pr_sdj_push_next, pr_sdj_push_bi/
qed.

(* Inversions with pr_isi ***************************************************)

(*** sdj_inv_refl *)
corec lemma pr_sdj_inv_refl:
            ∀f. f ∥ f →  𝐈❨f❩.
#f cases (pr_map_split_tl f) #Hf #H
[ lapply (pr_sdj_inv_push_bi … H … Hf Hf) -H /3 width=3 by pr_isi_push/
| elim (pr_sdj_inv_next_bi … H … Hf Hf)
]
qed-.
