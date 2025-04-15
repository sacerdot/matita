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

include "ground/subsets/subset_ol_le.ma".
include "delayed_updating/syntax/prototerm_clear_eq.ma".
include "delayed_updating/syntax/prototerm_clear_ol.ma".

(* CLEARED PROTOTERM ********************************************************)

(* Advanved constructions with subset_ol ************************************)

lemma term_ol_clear_slice_bi (p1) (p2):
      (⓪p1) ϵ ⓪▵↑p2 → ⓪↑p1 ≬ ⓪↑p2.
#p1 #p2 * #r1 * #q1 * #q2 #_ #H0 #H1 destruct
@(subset_ol_le_repl ????? (term_le_clear_slice …) ? (subset_le_refl …)) >H1 -H1
@(subset_ol_le_repl ????? (term_le_clear_slice_clear …) ? (subset_le_refl …))
/3 width=3 by ol_clear_bi, subset_ol_i/
qed.

(* Advanved inversions with subset_ol ***************************************)

lemma term_ol_inv_clear_slice_bi (p1) (p2):
      (⓪↑p1) ≬ ⓪↑p2 → ⓪p1 ϵ ⓪▵↑p2.
#p1 #p2 * #r * #s1 * #q1 #_ #H1 #H2 * #s2 * #q2 #_ #H3 #H4 destruct
<path_clear_append in H4; <path_clear_append #H0
>path_clear_idem
@term_le_clear_root
@(term_root_le_repl … (term_le_clear_slice …))
@term_le_root_clear
@in_comp_term_clear
@term_in_root [| >H0 ] -p1 -q1 //
qed-.

(* Advanced constructions ***************************************************)

lemma term_in_comp_clear_bi_root_slice_dec (p1) (p2):
      Decidable (⓪p1 ϵ ⓪▵↑p2).
#p1 #p2 elim (ol_clear_slice_bi_dec p1 p2) #H0
[ /3 width=1 by term_ol_inv_clear_slice_bi, or_introl/
| /4 width=1 by term_ol_clear_slice_bi, or_intror/
]
qed-.
