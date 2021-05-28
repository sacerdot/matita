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

include "ground/relocation/gr_isi_id.ma".
include "ground/relocation/gr_coafter_coafter.ma".

(* RELATIONAL CO-COMPOSITION FOR GENERIC RELOCATION MAPS ***********************************************************)

(* Properties with test for identity ****************************************)

(*** coafter_isid_sn *)
corec lemma gr_coafter_isi_sn:
            ∀f1. 𝐈❪f1❫ → ∀f2. f1 ~⊚ f2 ≘ f2.
#f1 * -f1 #f1 #g1 #Hf1 #H1 #f2
cases (gr_map_split_tl f2) #H2
/3 width=7 by gr_coafter_push, gr_coafter_refl/
qed.

(*** coafter_isid_dx *)
corec lemma gr_coafter_isi_dx:
            ∀f2,f. 𝐈❪f2❫ → 𝐈❪f❫ → ∀f1. f1 ~⊚ f2 ≘ f.
#f2 #f * -f2 #f2 #g2 #Hf2 #H2 * -f #f #g #Hf #H #f1
cases (gr_map_split_tl f1) #H1
[ /3 width=7 by gr_coafter_refl/
| @(gr_coafter_next … H1 … H) /3 width=3 by gr_isi_push/
]
qed.

(* Inversion lemmas with test for identity **********************************)

(*** coafter_isid_inv_sn *)
lemma gr_coafter_isi_inv_sn:
      ∀f1,f2,f. f1 ~⊚ f2 ≘ f → 𝐈❪f1❫ → f2 ≡ f.
/3 width=6 by gr_coafter_isi_sn, gr_coafter_mono/ qed-.

(*** coafter_isid_inv_dx *)
lemma gr_coafter_isi_inv_dx:
      ∀f1,f2,f. f1 ~⊚ f2 ≘ f → 𝐈❪f2❫ → 𝐈❪f❫.
/4 width=4 by gr_eq_id_isi, gr_coafter_isi_dx, gr_coafter_mono/ qed-.
