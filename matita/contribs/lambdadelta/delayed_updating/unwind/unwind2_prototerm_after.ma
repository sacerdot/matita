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

include "delayed_updating/unwind/unwind2_prototerm_eq.ma".
include "delayed_updating/unwind/unwind2_path_after.ma".

(* TAILED UNWIND FOR PROTOTERM **********************************************)

(* Constructions with tr_after **********************************************)

lemma unwind2_term_after (f1) (f2) (t):
      ▼[f2]▼[f1]t ⇔ ▼[f2∘f1]t.
#f1 #f2 #t @subset_eq_trans
[
| @subset_inclusion_ext_f1_compose
| @subset_equivalence_ext_f1_exteq /2 width=5/
]
qed.
