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

include "delayed_updating/reduction/prototerm_dbf_residuals.ma".
include "delayed_updating/notation/relations/epsilon_star_2.ma".
include "delayed_updating/notation/relations/neg_epsilon_star_2.ma".

(* MEMBERSHIP OF A TRACE TO A SUBSET OF DBF-REDEX POINTERS ******************)

rec definition term_ins_dbfr (rs) (u) on rs: Prop ≝
match rs with
[ list_empty      ⇒ ⊤
| list_lcons r rs ⇒ ∧∧ r ϵ u & term_ins_dbfr rs (u /𝐝𝐛𝐟 r)   
].

interpretation
  "trace membership (subset of dbf-redex pointers)"
  'EpsilonStar rs u = (term_ins_dbfr rs u).

interpretation
  "negated trace membership (subset of dbf-redex pointers)"
  'NegEpsilonStar rs u = (negation (term_ins_dbfr rs u)).

(* Basic constructions ******************************************************)

lemma term_ins_dbfr_empty (u):
      (ⓔ) ϵ* u.
//
qed.

lemma term_ins_dbfr_lcons (r) (rs) (u):
      r ϵ u → rs ϵ* u /𝐝𝐛𝐟 r → r⨮rs ϵ* u.
/2 width=1 by conj/
qed.
