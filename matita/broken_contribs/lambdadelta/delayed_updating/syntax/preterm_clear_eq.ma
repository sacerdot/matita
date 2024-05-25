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

include "ground/subsets/subset_eq.ma".
include "delayed_updating/syntax/preterm_clear.ma".

(* CLEARED PRETERM **********************************************************)

(* Constructions with subset_le *********************************************)

lemma term_le_clear_grafted_dx (t) (p):
      t ϵ 𝐓 → p ϵ ▵t → ⋔[⓪p]⓪t ⊆ ⓪⋔[p]t.
#t #p #Ht #Hp #r * #x #Hx #H0
elim (eq_inv_path_append_clear … H0) -H0 #q #s #H0 #H1 #H2 destruct
lapply (term_clear_inj … Ht … H0) -Ht -H0
[1,2: /2 width=2 by term_in_root/ ] -Hp #H0 destruct
/2 width=1 by in_comp_term_clear/
qed.

lemma term_le_clear_grafted_S_dx_dx (t) (p):
      t ϵ 𝐓 → p◖𝗔 ϵ ▵t → ⋔[⓪(p◖𝗦)]⓪t ⊆ ⓪⋔[p◖𝗦]t.
#t #p #Ht #Hp
/3 width=1 by term_le_clear_grafted_dx, term_full_A_post/
qed.
