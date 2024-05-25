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

include "ground/subsets/subset_listed.ma".
include "delayed_updating/syntax/prototerm_eq.ma".
include "delayed_updating/syntax/prototerm_clear.ma".

(* Constructions with equivalence for prototerm *****************************)

lemma clear_pt_append (p) (t):
      (⓪p)●(⓪t) ⇔ ⓪(p●t).
#p #t @conj #r * #s * #q #Hq #H1 #H2 destruct
/3 width=1 by pt_append_in, in_comp_term_clear/
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
