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

include "ground/lib/subset_full.ma".
include "delayed_updating/syntax/path.ma".
include "delayed_updating/notation/functions/category_t_0.ma".
include "delayed_updating/notation/functions/pitchfork_2.ma".
include "delayed_updating/notation/functions/uptriangle_1.ma".

(* PROTOTERM ****************************************************************)

(* Note: a prototerm is a subset of complete paths *)
interpretation
  "prototerm ()"
  'CategoryT = (predicate (list label)).

definition term_grafted (p) (t): 𝕋 ≝
           ❴q ❘ p●q ϵ t❵.

interpretation
  "grafted (prototerm)"
  'Pitchfork p t = (term_grafted p t).

definition term_root (t): 𝕋 ≝
           ❴p ❘ ∃q. q ϵ ⋔[p]t❵.

interpretation
  "root (prototerm)"
  'UpTriangle t = (term_root t).

definition pt_append (p) (t): 𝕋 ≝
           ❴r ❘ ∃∃q. q ϵ t & r = p●q❵.

interpretation
  "append (prototerm)"
  'BlackCircle p t = (pt_append p t).

interpretation
  "left_cons (prototerm)"
  'BlackHalfCircleRight l t = (pt_append (list_lcons label l (list_empty label)) t).

interpretation
  "slice (prototerm)"
  'UpArrow p = (pt_append p (subset_full ?)).

(* Basic inversions *********************************************************)

lemma term_grafted_inv_gen (t) (p) (q):
      q ϵ ⋔[p]t → p●q ϵ t.
// qed-.

lemma append_in_comp_inv_bi (p) (q) (t):
      p●q ϵ p●t → q ϵ t.
#p #q #t * #r #Hr #H0
>(eq_inv_list_append_dx_bi … H0) -p -q //
qed-.

lemma term_slice_inv_lcons_bi (p1) (p2) (l1) (l2):
      l1◗p1 ϵ ↑(l2◗p2) →
      ∧∧ l1 = l2 & p1 ϵ ↑p2.
#p1 #p2 #l1 #l2 *
#q <list_append_assoc #_ #H0
elim (eq_inv_list_rcons_bi ??? … H0) -H0
#H1 #H2 destruct
/3 width=3 by ex2_intro, conj/
qed-.

lemma term_le_antisym (p1) (p2):
      p1 ϵ ↑p2 → p2 ϵ ↑p1 → p1 = p2.
#p1 #p2 * #q2 #_ #H2 >H2 -p1 * #q1 #_
<list_append_assoc #H1
lapply (eq_inv_list_append_dx_dx_refl … H1) -H1 #H0
elim (eq_inv_list_empty_append … H0) -H0 #_ #H2 destruct //
qed-.

(* Basic constructions ******************************************************)

lemma term_in_root (t) (p) (q):
      p●q ϵ t → p ϵ ▵t.
/2 width=2 by ex_intro/
qed.

lemma term_in_comp_root (t) (p):
      p ϵ t → p ϵ ▵t.
/2 width=2 by term_in_root/
qed.

lemma pt_append_in (p) (q) (t):
      q ϵ t → p●q ϵ p●t.
/2 width=3 by ex2_intro/
qed.

lemma term_slice_in (p) (q):
      p●q ϵ ↑p.
/2 width=2 by pt_append_in/
qed.

lemma term_le_refl (p):
      p ϵ ↑p.
// qed.

lemma term_slice_append_sn (p) (q1) (q2):
      q1 ϵ ↑q2 → p●q1 ϵ ↑(p●q2).
#p #q1 #q2 * #r #H0 destruct //
qed.

(* Basic destructions *******************************************************)

lemma term_in_root_append_des_sn (t) (p) (q):
      p●q ϵ ▵t → p ϵ ▵t.
#t #p #q * #r #Hr
/2 width=2 by ex_intro/
qed-.
