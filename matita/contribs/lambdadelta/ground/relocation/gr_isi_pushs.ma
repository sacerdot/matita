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

include "ground/relocation/gr_pushs.ma".
include "ground/relocation/gr_isi.ma".

(* IDENTITY CONDITION FOR GENERIC RELOCATION MAPS ***************************)

(* Constructions with gr_pushs **********************************************)

(*** isid_pushs *)
lemma gr_isi_pushs (n) (f): 𝐈❪f❫ → 𝐈❪⫯*[n]f❫.
#n @(nat_ind_succ … n) -n /3 width=3 by gr_isi_push/
qed.

(* Inversions with gr_pushs *************************************************)

(*** isid_inv_pushs *)
lemma gr_isi_inv_pushs (n) (g): 𝐈❪⫯*[n]g❫ → 𝐈❪g❫.
#n @(nat_ind_succ … n) -n /3 width=3 by gr_isi_inv_push/
qed-.
