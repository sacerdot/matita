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
include "ground/lib/subset_ext_equivalence.ma".
include "delayed_updating/unwind_k/unwind2_path_eq.ma".
include "delayed_updating/unwind_k/unwind2_prototerm.ma".

(* TAILED UNWIND FOR PROTOTERM **********************************************)

(* Constructions with subset_equivalence ************************************)

lemma unwind2_term_eq_repl_sn (f1) (f2) (t):
      f1 ≗ f2 → ▼[f1]t ⇔ ▼[f2]t.
/3 width=1 by subset_equivalence_ext_f1_exteq, unwind2_path_eq_repl/
qed.

lemma unwind2_term_eq_repl_dx (f) (t1) (t2):
      t1 ⇔ t2 → ▼[f]t1 ⇔ ▼[f]t2.
/2 width=1 by subset_equivalence_ext_f1_bi/
qed.
