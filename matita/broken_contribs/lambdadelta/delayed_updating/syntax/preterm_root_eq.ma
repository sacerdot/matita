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

include "delayed_updating/syntax/path_root_eq.ma".
include "delayed_updating/syntax/preterm.ma".

(* PRETERM ******************************************************************)

(* Inversions with path_root_le *********************************************)

lemma path_rle_inv_complete_head_dx (t) (p1) (p2):
      t ϵ 𝐓 → p1 ϵ t → p2 ϵ ▵t →
      p1 ⊑ p2 → p1 = p2.
#t #p1 #p2 #Ht #Hp1 * #q2 #Hq2 #Hp
lapply (term_grafted_inv_gen … Hq2) -Hq2 #Hq2
elim (term_in_slice_inv_gen … Hp) -Hp #q1 #H0 destruct
<list_append_assoc in Hq2; #Hq2
lapply (term_complete_append … Ht Hp1 Hq2) -t #H0
elim (eq_inv_list_empty_append … H0) -H0 #_ #H0 destruct -q2 //
qed-.

lemma path_rle_inv_complete (t) (p1) (p2):
      t ϵ 𝐓 → p1 ϵ t → p2 ϵ t →
      p1 ⊑ p2 → p2 = p1.
#t #p1 #p2 #Ht #Hp1 #Hp2 #H0
/2 width=4 by term_complete_post/
qed-.

(* Inversions with path_root_eq *********************************************)

lemma path_req_inv_complete_head_sx (t) (p1) (p2):
      t ϵ 𝐓 → p1 ϵ t → p2 ϵ ▵t →
      p2 ≚ p1 → p2 ⊑ p1.
#t #p1 #p2 #Ht #Hp1 #Hp2 * #Hp //
<(path_rle_inv_complete_head_dx ??? Ht ?? Hp) //
qed-.

lemma path_req_inv_complete (t) (p1) (p2):
      t ϵ 𝐓 → p1 ϵ t → p2 ϵ t →
      p1 ≚ p2 → p1 = p2.
#t #p1 #p2 #Ht #Hp1 #Hp2 * #Hp
<(path_rle_inv_complete … Ht … Hp) -Ht -Hp //
qed-.
