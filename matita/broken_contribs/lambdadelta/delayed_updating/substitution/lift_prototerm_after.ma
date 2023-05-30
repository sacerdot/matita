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

include "delayed_updating/substitution/lift_prototerm_eq.ma".
include "delayed_updating/substitution/lift_path_after.ma".

(* LIFT FOR PROTOTERM *******************************************************)

(* Constructions with tr_after **********************************************)

lemma lift_term_after (f) (g) (t):
      🠡[g]🠡[f]t ⇔ 🠡[g•f]t.
#f #g #t @subset_eq_trans
[
| @subset_inclusion_ext_f1_compose
| @subset_equivalence_ext_f1_exteq
  #p <lift_path_after //
]
qed.
