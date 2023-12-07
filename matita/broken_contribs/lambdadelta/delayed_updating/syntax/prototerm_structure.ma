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
include "delayed_updating/syntax/path_structure.ma".
include "ground/lib/subset_ext.ma".

(* STRUCTURE FOR PROTOTERM **************************************************)

interpretation
  "structure (prototerm)"
  'CircledTimes t = (subset_ext_f1 ?? structure t).

(* Basic constructions ******************************************************)

lemma in_comp_structure_bi (t) (p):
      p ϵ t → ⊗p ϵ ⊗t.
/2 width=1 by subset_in_ext_f1_dx/
qed.

lemma in_root_structure_bi (t) (p):
      p ϵ ▵t → ⊗p ϵ ▵⊗t.
#t #p * #q #Hq
/3 width=3 by in_comp_structure_bi, term_in_root/
qed.

(* Basic inversions *********************************************************)

lemma term_in_comp_structure_grafted_inv_d_dx (t) (p) (q) (k):
      q ϵ ⋔[p◖𝗱k]⊗t → ⊥.
#t #p #q #k * #r #_ #H0 -t
elim (eq_inv_append_structure … (sym_eq … H0)) -H0 #s1 #s2 #H0 #_ #_ 
elim (eq_inv_d_dx_structure … H0)
qed-.

lemma term_in_comp_structure_grafted_inv_rcons (t) (p1) (q1) (l):
      (∀k. 𝗱k = l → ⊥) →
      q1 ϵ ⋔ [p1◖l]⊗t →
      ∃∃p2,q2. q2 ϵ ⋔ [p2◖l]t & p1 = ⊗p2 & q1 = ⊗q2.
#t #p1 #q1 #l #Hl * #r1 #Hr1 #H0
elim (eq_inv_append_structure … (sym_eq … H0)) -H0 #x2 #q2 #H0 #H1 #H2 destruct
elim (eq_inv_rcons_structure … Hl … H0) -Hl -H0
#p2 #r2 #H1 #Hr2 #H2 destruct
<list_append_rcons_sn in Hr1; <list_append_assoc #Hr1
@(ex3_2_intro … p2 (r2●q2)) // -t -p2 -l
<structure_append <Hr2 -r2 //
qed-.

lemma term_in_root_structure_inv_d_dx (t) (p) (k):
      p◖𝗱k ϵ ▵⊗t → ⊥.
#t #p #k * #q #H0
elim (term_in_comp_structure_grafted_inv_d_dx … H0)
qed-.

lemma term_in_root_strucrure_inv_rcons (t) (p1) (l):
      (∀k. 𝗱k = l → ⊥) →
      p1◖l ϵ ▵⊗t →
      ∃∃p2. p2◖l ϵ ▵t & p1 = ⊗p2.
#t #p1 #l #Hl * #q1 #Hq1
elim (term_in_comp_structure_grafted_inv_rcons … Hl … Hq1) -Hl -Hq1
#p2 #q2 #Hq2 #Hp2 #H0 destruct
/3 width=3 by term_in_root, ex2_intro/
qed-.
