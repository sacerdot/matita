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
include "delayed_updating/substitution/lift_after.ma".
include "delayed_updating/substitution/lift_prototerm.ma".

(* LIFT FOR PROTOTERM *******************************************************)

(* Constructions with subset_equivalence ************************************)

lemma lift_term_eq_repl_sn (f1) (f2) (t):
      f1 ≗ f2 → ↑[f1]t ⇔ ↑[f2]t.
/3 width=1 by subset_equivalence_ext_f1_exteq, lift_path_eq_repl/
qed.

lemma lift_term_eq_repl_dx (f) (t1) (t2):
      t1 ⇔ t2 → ↑[f]t1 ⇔ ↑[f]t2.
/2 width=1 by subset_equivalence_ext_f1_bi/
qed.

lemma lift_term_after (f1) (f2) (t):
      ↑[f2]↑[f1]t ⇔ ↑[f2∘f1]t.
#f1 #f2 #t @subset_eq_trans
[
| @subset_inclusion_ext_f1_compose
| @subset_equivalence_ext_f1_exteq /2 width=5/
]
qed.

lemma lift_term_id_sn (t):
      t ⊆ ↑[𝐢]t.
#t #p #Hp
>(lift_path_id p)
/2 width=1 by in_comp_lift_bi/
qed-.

lemma lift_term_id_dx (t):
      ↑[𝐢]t ⊆ t.
#t #p * #q #Hq #H destruct //
qed-.

lemma lift_term_id (t):
      t ⇔ ↑[𝐢]t.
/3 width=2 by lift_term_id_dx, lift_term_id_sn, conj/
qed.
