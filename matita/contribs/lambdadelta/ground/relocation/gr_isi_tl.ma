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
include "ground/relocation/gr_isi.ma".

(* IDENTITY CONDITION FOR GENERIC RELOCATION MAPS ***************************)

(* Constructions with gr_tl *************************************************)

(*** isid_tl *)
lemma gr_isi_tl (f): 𝐈❪f❫ → 𝐈❪⫱f❫.
#f cases (gr_map_split_tl f) * #H
[ /2 width=3 by gr_isi_inv_push/
| elim (gr_isi_inv_next … H) -H //
]
qed.
