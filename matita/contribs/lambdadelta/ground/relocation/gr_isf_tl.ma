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
include "ground/relocation/gr_isf.ma".

(* FINITE COLENGTH CONDITION FOR GENERIC RELOCATION MAPS ********************)

(* Constructions with gr_tl *************************************************)

(*** isfin_tl *)
lemma gr_isf_tl (f): 𝐅❪f❫ → 𝐅❪⫱f❫.
#f elim (gr_map_split_tl f) * #Hf
/3 width=3 by gr_isf_inv_push, gr_isf_inv_next/
qed.

(* Inversions with gr_tl ****************************************************)

(*** isfin_inv_tl *)
lemma gr_isf_inv_tl (g): 𝐅❪⫱g❫ → 𝐅❪g❫.
#f elim (gr_map_split_tl f) * #Hf
/2 width=1 by gr_isf_next, gr_isf_push/
qed-.
