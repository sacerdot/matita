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

include "delayed_updating/substitution/fsubst.ma".
include "delayed_updating/substitution/lift_prototerm_ol.ma".
include "delayed_updating/substitution/lift_prototerm_eq.ma".

(* FOCALIZED SUBSTITUTION ***************************************************)

(* Constructions with lift for preterm **************************************)

lemma lift_term_fsubst_sx (f) (t) (u1) (u2):
      ⬕[🠡[f]u1←🠡[f]u2]🠡[f]t ⊆ 🠡[f]⬕[u1←u2]t.
#f #t #u1 #u2 #r * *
[ /4 width=3 by fsubst_in_comp_true, term_ol_inv_lift_bi, lift_term_le_repl_dx/
| * #s #Hs #H1 #H0 destruct
  /5 width=1 by fsubst_in_comp_false, in_comp_lift_bi/
]
qed-.

lemma lift_term_fsubst_dx (f) (t) (u1) (u2):
      (🠡[f]⬕[u1←u2]t) ⊆ ⬕[🠡[f]u1←🠡[f]u2]🠡[f]t.
#f #t #u1 #u2 #r * #s * *
[ #H0 #Hs #H1 destruct
  /3 width=1 by fsubst_in_comp_true, term_ol_lift_bi, in_comp_lift_bi/
| #Hs #H0 #H1 destruct
  /4 width=2 by fsubst_in_comp_false, in_comp_inv_lift_bi, in_comp_lift_bi/
]
qed-.

lemma lift_term_fsubst (f) (t) (u1) (u2):
      ⬕[🠡[f]u1←🠡[f]u2]🠡[f]t ⇔ 🠡[f]⬕[u1←u2]t.
/3 width=1 by lift_term_fsubst_sx, conj, lift_term_fsubst_dx/
qed.
