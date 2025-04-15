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

include "delayed_updating/syntax/path_clear.ma".
include "delayed_updating/syntax/prototerm.ma".

(* CLEARED PROTOTERM ********************************************************)

definition term_clear (t): (𝕋) ≝
           {r | ∃∃p. p ϵ t & r = ⓪p}
.

interpretation
  "clear (prototem)"
  'CircledZero t = (term_clear t).

(* Basic constructions ******************************************************)

lemma in_comp_term_clear (p) (t):
      p ϵ t → ⓪p ϵ ⓪t.
/2 width=3 by ex2_intro/
qed.

(* Advanced constructions ***************************************************)

lemma in_comp_term_clear_d_dx (p) (t) (k):
      p◖𝗱k ϵ t → (⓪p)◖𝗱𝟎 ϵ ⓪t.
/2 width=2 by in_comp_term_clear/
qed.

(* Constructions with path_clear ********************************************)

lemma term_slice_clear (p1) (p2):
      p1 ϵ ↑p2 → ⓪p1 ϵ ↑⓪p2.
#p1 #p2 * #q2 #_ #H0 destruct //
qed.

(* Inversions with path_clear ***********************************************)

lemma in_comp_inv_term_empty_clear (t):
      (𝐞) ϵ ⓪t → (𝐞) ϵ t.
#t * #p #Hp #H0
lapply (eq_inv_path_empty_clear … H0) -H0 #H0 destruct //
qed-.

lemma term_slice_antisym_clear (p1) (p2):
      ⓪p1 ϵ ↑⓪p2 → p2 ϵ ↑p1 → p1 = p2.
#p1 #p2 * #q2 #_ #Hq2 * #q1 #_ #H0 destruct
<path_clear_append in Hq2; <list_append_assoc #H0
lapply (eq_inv_list_append_dx_dx_refl … H0) -H0 #H0
elim (eq_inv_list_empty_append … H0) -H0 #_ #H0 -q2
<(eq_inv_path_empty_clear … H0) -q1 //
qed-.

lemma in_comp_slice_clear_inv_clear_sx (p1) (p2):
      (⓪p1) ϵ ↑⓪p2 → ⓪p1 ϵ ⓪↑p2.
#p1 #p2 * #s2 #_ #H0
elim (eq_inv_path_append_clear … (sym_eq … H0)) -H0 #r2 #s1 #H0 #H1 #H2 destruct
<path_clear_append <H0 -r2
/2 width=1 by in_comp_term_clear/
qed-.
