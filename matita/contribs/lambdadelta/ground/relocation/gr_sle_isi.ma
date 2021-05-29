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

include "ground/relocation/gr_isi.ma".
include "ground/relocation/gr_sle.ma".

(* INCLUSION FOR GENERIC RELOCATION MAPS ************************************)

(* Constructions with gr_isi ************************************************)

(*** sle_isid_sn *)
corec lemma gr_sle_isi_sn:
            ∀f1. 𝐈❪f1❫ → ∀f2. f1 ⊆ f2.
#f1 * -f1
#f1 #g1 #Hf1 #H1 #f2 cases (gr_map_split_tl f2) *
/3 width=5 by gr_sle_weak, gr_sle_push/
qed.

(* Inversions with gr_isi ***************************************************)

(*** sle_inv_isid_dx *)
corec lemma gr_sle_inv_isi_dx:
            ∀f1,f2. f1 ⊆ f2 → 𝐈❪f2❫ → 𝐈❪f1❫.
#f1 #f2 * -f1 -f2
#f1 #f2 #g1 #g2 #Hf * * #H
[2,3: elim (gr_isi_inv_next … H) // ]
lapply (gr_isi_inv_push … H ??) -H
/3 width=3 by gr_isi_push/
qed-.
