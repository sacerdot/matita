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
include "ground/relocation/gr_isu.ma".

(* UNIFORMITY CONDITION FOR GENERIC RELOCATION MAPS *************************)

(* Constructions with gr_tl *************************************************)

lemma gr_isu_tl (f): 𝐔❪f❫ → 𝐔❪⫱f❫.
#f cases (gr_map_split_tl f) * #H
[ /3 width=3 by gr_isu_inv_push, gr_isu_isi/
| /2 width=3 by gr_isu_inv_next/
]
qed.

(* Advanced inversions ******************************************************)

(*** isuni_split *)
lemma gr_isu_split (g): 𝐔❪g❫ → ∨∨ (∃∃f. 𝐈❪f❫ & ⫯f = g) | (∃∃f.𝐔❪f❫ & ↑f = g).
#g elim (gr_map_split_tl g) * #H
/4 width=3 by gr_isu_inv_next, gr_isu_inv_push, or_introl, or_intror, ex2_intro/
qed-.
