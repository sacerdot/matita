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

include "ground/lib/functions.ma".
include "ground/subsets/subset_and.ma".
include "ground/subsets/subset_listed.ma".
include "delayed_updating/syntax/prototerm_eq.ma".
include "delayed_updating/syntax/prototerm_clear.ma".

(* CLEARED PROTOTERM ********************************************************)

(* Constructions with subset_le *********************************************)

lemma clear_le_repl:
      compatible_2_fwd … (subset_le …) (subset_le …) (term_clear).
#t1 #t2 #Ht12 #zp * #p #Hp #H0 destruct
/3 width=1 by in_comp_term_clear/
qed.

(* Note: the other inclusion does not hold as is *)
lemma clear_and_dx (t1) (t2):
      ⓪(t1 ∩ t2) ⊆ (⓪t1) ∩ (⓪t2).
#t1 #t2 #pz * #p * #H1p #H2p #H0 destruct
/3 width=1 by in_comp_term_clear, subset_and_in/
qed.

lemma term_le_root_clear (t):
      (⓪▵t) ⊆ ▵⓪t.
#t #r * #p * #q #Hq #H0 destruct
/3 width=2 by in_comp_term_clear, term_in_root/
qed.

lemma term_le_clear_root (t):
      ▵⓪t ⊆ ⓪▵t.
#t #r * #s #H0
lapply (term_grafted_inv_gen … H0) -H0 * #x #Hx #H0
elim (eq_inv_path_append_clear … H0) -H0 #p #q #H1 #H2 #H3 destruct
/3 width=2 by in_comp_term_clear, term_in_root/
qed.

lemma term_le_clear_slice_clear (p):
      (⓪↑p) ⊆ ⓪↑⓪p.
#p #r * #s * #q #_ #H1 #H2 destruct
>path_clear_idem in ⊢ (???%); <path_clear_append
/2 width=1 by in_comp_term_clear/
qed.

lemma term_le_clear_slice (p):
      (⓪↑⓪p) ⊆ ⓪↑p.
#p #r * #s * #q #_ #H1 #H2 destruct
<path_clear_append <path_clear_idem >path_clear_append
/2 width=1 by in_comp_term_clear/
qed.

lemma term_le_slice_clear (p):
      (⓪↑p) ⊆ ↑⓪p.
#p #r * #s * #q #_ #H1 #H2 destruct
<path_clear_append //
qed.

(* Constructions with subset_eq *********************************************)

lemma clear_eq_repl:
      compatible_2_fwd … (subset_eq …) (subset_eq …) (term_clear).
#t1 #t2 * #Ht12 #Ht21
/3 width=3 by clear_le_repl, conj/
qed.

lemma clear_pt_append (p) (t):
      (⓪p)●(⓪t) ⇔ ⓪(p●t).
#p #t @conj #r * #s * #q #Hq #H1 #H2 destruct
/3 width=1 by pt_append_in, in_comp_term_clear/
qed.

lemma term_eq_clear_slice_clear (p):
      (⓪↑p) ⇔ ⓪↑⓪p.
#p @conj
/2 width=1 by term_le_clear_slice_clear, term_le_clear_slice/
qed.

lemma clear_single (p):
      ❴⓪p❵ ⇔ ⓪❴p❵.
#p @conj #r *
[ #q1 #q2 #H0
  elim (eq_inv_list_lcons_append ????? (sym_eq … H0)) -H0 *
  [ #_ #H0 destruct -q1 /2 width=1 by in_comp_term_clear/
  | #q #_ #H0 -q1
    elim (eq_inv_list_empty_append … H0) #_ #H0 -q destruct
  ]
| #s * #q1 #q2 #H0 #H1 destruct
  elim (eq_inv_list_lcons_append ????? (sym_eq … H0)) -H0 *
  [ #_ #H0 destruct -q1 //
  | #q #_ #H0 -q1
    elim (eq_inv_list_empty_append … H0) #_ #H0 -q destruct
  ]
]
qed.
