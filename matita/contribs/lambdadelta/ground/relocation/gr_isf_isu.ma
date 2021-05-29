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

include "ground/relocation/gr_isu.ma".
include "ground/relocation/gr_isf.ma".

(* FINITE COLENGTH CONDITION FOR GENERIC RELOCATION MAPS ********************)

(* Constructions with gr_isu ************************************************)

(*** isuni_fwd_isfin *)
lemma gr_isf_isu (f): 𝐔❪f❫ → 𝐅❪f❫.
#f #H elim H -f
/3 width=1 by gr_isf_next, gr_isf_isi/
qed.
