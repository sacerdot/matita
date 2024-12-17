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

include "explicit_updating/syntax/term_next_eq.ma".
include "explicit_updating/syntax/term_nexts.ma".

(* ITERATED NEXT FOR TERM ***************************************************)

(* Constructions with term_eq ***********************************************)

lemma term_nexts_eq_repl:
      compatible_3 … (eq …) term_eq term_eq term_nexts.
#n1 #n2 #Hn destruct
@(nat_ind_succ … n2) -n2
/3 width=1 by term_next_eq_repl/
qed.

(* Inversions with term_eq **************************************************)

lemma term_eq_inv_nexts_unit_bi (n1) (n2):
      ↑*[n1]𝛏 ≐ ↑*[n2]𝛏 → n1 = n2.
@nat_ind_succ
[ @nat_ind_succ // #n2 #_
  <term_nexts_succ #H0
  lapply (term_eq_inv_unit_sx … H0) -H0
  <term_next_unfold #H0 destruct
| #n1 #IH @nat_ind_succ
  [ <term_nexts_succ #H0
    elim (term_eq_inv_lift_sx … H0) -H0 #f #x #_ #_
    <term_nexts_zero #H0 destruct
  | #n2 #_ <term_nexts_succ <term_nexts_succ #H0
    lapply (term_eq_inv_next_bi … H0) -H0 #H0 
    <(IH … H0) -n2 -IH //
  ]
]
qed-.
