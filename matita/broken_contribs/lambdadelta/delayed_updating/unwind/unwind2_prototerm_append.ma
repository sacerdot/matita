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

include "delayed_updating/syntax/prototerm_eq.ma".
include "delayed_updating/unwind/unwind2_path_append.ma".
include "delayed_updating/unwind/unwind2_prototerm.ma".

(* TAILED UNWIND FOR PROTOTERM **********************************************)

(* Constructions with append and pic ****************************************)

lemma unwind2_pt_append_pic_sn_sn (f) (p) (u): p ϵ 𝐈 →
      (⊗p)●(▼[▶[p]f]u) ⊆ ▼[f](p●u).
#f #p #u #Hp #r * #q * #s #Hs #H1 #H2 destruct
>unwind2_path_append_pic_sn
/3 width=1 by in_comp_unwind2_bi, pt_append_in/
qed-.

lemma unwind2_pt_append_pic_sn_dx (f) (p) (u): p ϵ 𝐈 →
      ▼[f](p●u) ⊆ (⊗p)●(▼[▶[p]f]u).
#f #p #u #Hp #r * #q * #s #Hs #H1 #H2 destruct
<unwind2_path_append_pic_sn
/3 width=1 by in_comp_unwind2_bi, pt_append_in/
qed-.

lemma unwind2_pt_append_pic_sn (f) (p) (u): p ϵ 𝐈 →
      (⊗p)●(▼[▶[p]f]u) ⇔ ▼[f](p●u).
/3 width=1 by conj, unwind2_pt_append_pic_sn_sn, unwind2_pt_append_pic_sn_dx/
qed.

(* Constructions with append and tpc ****************************************)

lemma unwind2_pt_append_tpc_dx_sn (f) (p) (u): u ⊆ 𝐏 →
      (⊗p)●(▼[▶[p]f]u) ⊆ ▼[f](p●u).
#f #p #u #Hu #r * #q * #s #Hs #H1 #H2 destruct
>unwind2_path_append_ppc_dx
/3 width=1 by in_comp_unwind2_bi, pt_append_in, subset_in_le_trans/
qed-.

lemma unwind2_pt_append_tpc_dx_dx (f) (p) (u): u ⊆ 𝐏 →
      ▼[f](p●u) ⊆ (⊗p)●(▼[▶[p]f]u).
#f #p #u #Hu #r * #q * #s #Hs #H1 #H2 destruct
<unwind2_path_append_ppc_dx
/3 width=1 by in_comp_unwind2_bi, pt_append_in, subset_in_le_trans/
qed-.

lemma unwind2_pt_append_tpc_dx (f) (p) (u): u ⊆ 𝐏 →
      (⊗p)●(▼[▶[p]f]u) ⇔ ▼[f](p●u).
/3 width=1 by conj, unwind2_pt_append_tpc_dx_sn, unwind2_pt_append_tpc_dx_dx/
qed.
