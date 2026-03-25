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

include "delayed_updating/syntax/preterm_clear.ma".
include "delayed_updating/syntax/preterm_root_eq.ma".

(* PRETERM ******************************************************************)

(* Inversions with path_clear and path_root_le ******************************)

lemma path_rle_in_root_inv_clear_bi (t) (p1) (p2):
      t ϵ 𝐓 → p1 ϵ ▵t → p2 ϵ ▵t → ⓪p1 ⊑ ⓪p2 → p1 ⊑ p2.
#t #p1 #p2 #Ht #Hp1 #Hp2 #Hp12
@(term_slice_des_clear_bi … Ht … Hp12) -Hp12 //
qed-.

(* Inversions with path_clear and path_root_eq ******************************)

lemma path_req_in_root_inv_clear_bi (t) (p1) (p2):
      t ϵ 𝐓 → p1 ϵ ▵t → p2 ϵ ▵t → ⓪p1 ≚ ⓪p2 → p1 ≚ p2.
#t #p1 #p2 #Ht #Hp1 #Hp2 * #Hp
/3 width=4 by path_req_mk_ge, path_req_mk_le, path_rle_in_root_inv_clear_bi/
qed-.

lemma path_req_in_comp_inv_clear_bi (t) (p1) (p2):
      t ϵ 𝐓 → p1 ϵ t → p2 ϵ t → ⓪p1 ≚ ⓪p2 → p1 = p2.
#t #p1 #p2 #Ht #Hp1 #Hp2 #Hp
@(term_clear_inj … Ht)
[1,2: /2 width=1 by term_in_comp_root/ ]
@(path_req_inv_complete (⓪t) … Hp) -Hp
/2 width=1 by preterm_clear, in_comp_term_clear/
qed-.
