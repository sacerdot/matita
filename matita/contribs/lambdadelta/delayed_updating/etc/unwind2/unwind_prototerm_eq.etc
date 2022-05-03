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

include "ground/lib/subset_ext_equivalence.ma".
include "delayed_updating/unwind2/unwind_eq.ma".
include "delayed_updating/unwind2/unwind_prototerm.ma".

(* UNWIND FOR PROTOTERM *****************************************************)

(* Constructions with subset_equivalence ************************************)

lemma unwind_term_eq_repl_sn (f1) (f2) (t):
      f1 ≗ f2 → ▼[f1]t ⇔ ▼[f2]t.
/3 width=1 by subset_equivalence_ext_f1_exteq, unwind_path_eq_repl/
qed.

lemma unwind_term_eq_repl_dx (f) (t1) (t2):
      t1 ⇔ t2 → ▼[f]t1 ⇔ ▼[f]t2.
/2 width=1 by subset_equivalence_ext_f1_bi/
qed.

lemma unwind_term_after (f1) (f2) (t):
      ▼[f2]▼[f1]t ⇔ ▼[f2∘f1]t.
#f1 #f2 #t @subset_eq_trans
[
| @subset_inclusion_ext_f1_compose
| @subset_equivalence_ext_f1_exteq /2 width=5/
]
qed.
