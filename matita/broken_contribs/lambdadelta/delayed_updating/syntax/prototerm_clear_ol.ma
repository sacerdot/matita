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

include "ground/subsets/subset_ol.ma".
include "ground/xoa/ex_1_2.ma".
include "ground/notation/xoa/ex_1_2_typed.ma".
include "delayed_updating/syntax/prototerm_clear.ma".

(* CLEARED PROTOTERM ********************************************************)

(* Constructions with subset_ol *********************************************)

lemma term_ol_clear_slice_bi_dec (p1) (p2):
      Decidable (⓪↑p1 ≬ ⓪↑p2).
#p1 #p2
elim (term_in_slice_dec (⓪p2) (⓪p1)) #Hp12
[| elim (term_in_slice_dec (⓪p1) (⓪p2)) #Hp21 ]
[ /4 width=3 by in_comp_slice_clear_inv_clear_sx, in_comp_term_clear, subset_ol_i, or_introl/
| /4 width=3 by in_comp_slice_clear_inv_clear_sx, in_comp_term_clear, subset_ol_i, or_introl/
| @or_intror * #x * #r1 * #q1 #_ #H1 #H2 * #r2 * #q2 #_ #H3 #H4 destruct
  <path_clear_append in H4; <path_clear_append #H0
  elim (eq_inv_list_append_bi … H0) -H0 * #r #H1r #H2r
  /2 width=1 by/
]
qed-.

lemma term_ol_clear_bi (t1) (t2):
      t1 ≬ t2 → (⓪t1) ≬ (⓪t2).
#t1 #t2 * #s #H1s #H2s
/3 width=3 by subset_ol_i, in_comp_term_clear/
qed.

(* Inversions with subset_ol ************************************************)

lemma term_ol_clear_slice_bi_inv_gen (p1) (p2):
      (⓪↑p1 ≬ ⓪↑p2) →
      ∃∃q1:ℙ,q2:ℙ. ⓪p1●⓪q1 = ⓪p2●⓪q2.
#p1 #p2 * #r * #s1 * #q1 #_ #H1 #H2 * #s2 * #q2 #_ #H3 #H4 destruct
<path_clear_append in H4; <path_clear_append; #H0
/2 width=3 by ex1_2_intro/
qed-.
