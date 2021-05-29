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
include "ground/relocation/gr_pat_pat_id.ma".

(* IDENTITY CONDITION FOR GENERIC RELOCATION MAPS ***************************)

(* Advanced constructions with gr_isi ***************************************)

(*** isid_at *)
lemma gr_isi_pat (f): (∀i. @❪i,f❫ ≘ i) → 𝐈❪f❫.
/3 width=1 by gr_eq_id_isi, gr_pat_inv_id/
qed.

(* Inversions with gr_pat ***************************************************)

(*** isid_inv_at *)
lemma gr_isi_inv_pat (f) (i): 𝐈❪f❫ → @❪i,f❫ ≘ i.
/3 width=3 by gr_isi_inv_eq_id, gr_pat_id, gr_pat_eq_repl_back/
qed-.

(* Destructions with gr_pat *************************************************)

(*** isid_inv_at_mono *)
lemma gr_isi_pat_des (f) (i1) (i2): 𝐈❪f❫ → @❪i1,f❫ ≘ i2 → i1 = i2.
/4 width=3 by gr_isi_inv_eq_id, gr_pat_id_des, gr_pat_eq_repl_fwd/
qed-.
