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

include "delayed_updating/syntax/prototerm.ma".
include "delayed_updating/syntax/path_proper.ma".
include "ground/lib/subset_inclusion.ma".

(* PROPER CONDITION FOR PROTOTERM *******************************************)

(* Basic constructions ******************************************************)

lemma tpc_in (t):
      (𝐞 ⧸ϵ t) → t ⊆ 𝐏.
/2 width=1 by/
qed.

(* Basic inversions *********************************************************)

(* Note: 𝒫❨path❩ fixes δ-expansion in tpc_pt_append_sn *)
lemma tpc_inv_empty (t:𝒫❨path❩):
      (𝐞) ϵ t → t ⊆ 𝐏 → ⊥.
/3 width=5 by subset_in_le_trans, ppc_inv_empty/
qed-.

(* Constructions with pt_append *********************************************)

lemma tpc_pt_append_dx (p) (t):
      p ϵ 𝐏 → p●t ⊆ 𝐏.
#p #t #Hp
@tpc_in * #q #_ #H0
elim (eq_inv_list_append_empty … H0) -H0 #_ #H0 destruct -q
/2 width=1 by ppc_inv_empty/
qed.

lemma tpc_pt_append_sn (p) (t):
      t ⊆ 𝐏 → p●t ⊆ 𝐏.
#p #t #Hp
@tpc_in * #q #Hq #H0
elim (eq_inv_list_append_empty … H0) -H0 #H0 #_ destruct -p
/2 width=3 by tpc_inv_empty/
qed.
