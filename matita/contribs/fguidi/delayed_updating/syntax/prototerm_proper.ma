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
include "ground/lib/subset_ext_equivalence.ma".

(* PROPER CONDITION FOR PROTOTERM *******************************************)

interpretation
  "proper condition (prototerm)"
  'ClassP = (subset_ext_p1 path ppc).

(* Basic constructions ******************************************************)

lemma tpc_in (t):
      (𝐞 ⧸ϵ t) → t ϵ 𝐏.
#t #Ht * //
#H elim (Ht H)
qed.

(* Basic destructions *******************************************************)

lemma in_comp_tpc_trans (t) (p):
      p ϵ t → t ϵ 𝐏 → p ϵ 𝐏.
#t #p #Hp #Ht
@(Ht … Hp)
qed-.

(* Basic inversions *********************************************************)

lemma tpc_inv_empty (t):
      (𝐞) ϵ t → t ϵ 𝐏 → ⊥.
/2 width=5 by in_comp_tpc_trans/ qed-.

(* Constructions with pt_append *********************************************)

lemma tpc_pt_append_dx (p) (t:prototerm):
      p ϵ 𝐏 → p●t ϵ 𝐏.
#p #t #Hp
@tpc_in * #q #_ #H0
elim (eq_inv_list_append_empty … H0) -H0 #_ #H0 destruct -q
/2 width=1 by ppc_inv_empty/
qed.

lemma tpc_pt_append_sn (p) (t:prototerm):
      t ϵ 𝐏 → p●t ϵ 𝐏.
#p #t #Hp
@tpc_in * #q #Hq #H0
elim (eq_inv_list_append_empty … H0) -H0 #H0 #_ destruct -p
/2 width=3 by tpc_inv_empty/
qed.
