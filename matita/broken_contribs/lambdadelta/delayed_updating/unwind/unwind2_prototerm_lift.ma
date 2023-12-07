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

(**) (* reverse include *)
include "ground/lib/subset_ext_eq.ma".
include "delayed_updating/substitution/lift_prototerm.ma".
include "delayed_updating/unwind/unwind2_path_lift.ma".
include "delayed_updating/unwind/unwind2_prototerm.ma".

(* TAILED UNWIND FOR PROTOTERM **********************************************)

(* Constructions with lift_prototerm ****************************************)

lemma lift_unwind2_term_after (f1) (f2) (t):
      🠡[f2]▼[f1]t ⇔ ▼[f2•f1]t.
#f1 #f2 #t @subset_eq_trans
[| @subset_le_ext_f1_compose ]
@subset_eq_ext_f1_exteq #p
@lift_unwind2_path_after
qed.

lemma unwind2_lift_term_after (f1) (f2) (t):
      ▼[f2]🠡[f1]t ⇔ ▼[f2•f1]t.
#f1 #f2 #t @subset_eq_trans
[| @subset_le_ext_f1_compose ]
@subset_eq_ext_f1_exteq #p
@unwind2_lift_path_after
qed.
