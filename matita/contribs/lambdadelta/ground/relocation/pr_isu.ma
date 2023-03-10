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

include "ground/notation/relations/predicate_u_1.ma".
include "ground/relocation/pr_isi.ma".

(* UNIFORMITY CONDITION FOR PARTIAL RELOCATION MAPS *************************)

(*** isuni *)
inductive pr_isu: predicate pr_map ā
(*** isuni_isid *)
| pr_isu_isi (f): šāØfā© ā pr_isu f
(*** isuni_next *)
| pr_isu_next (f): pr_isu f ā āg. āf = g ā pr_isu g
.

interpretation
  "uniformity condition (partial relocation maps)"
  'PredicateU f = (pr_isu f).

(* Basic inversions *********************************************************)

(*** isuni_inv_push *)
lemma pr_isu_inv_push (g): šāØgā© ā āf. ā«Æf = g ā šāØfā©.
#g * -g
[ /2 width=3 by pr_isi_inv_push/
| #f #_ #g #H #x #Hx destruct
  elim (eq_inv_pr_push_next ā¦ Hx)
]
qed-.

(*** isuni_inv_next *)
lemma pr_isu_inv_next (g): šāØgā© ā āf. āf = g ā šāØfā©.
#g * -g #f #Hf
[ #x #Hx elim (pr_isi_inv_next ā¦ Hf ā¦ Hx)
| #g #H #x #Hx destruct
  >(eq_inv_pr_next_bi ā¦ Hx) -x //
]
qed-.

(* Basic destructions *******************************************************)

(*** isuni_fwd_push *)
lemma pr_isu_fwd_push (g): šāØgā© ā āf. ā«Æf = g ā šāØfā©.
/3 width=3 by pr_isu_inv_push, pr_isu_isi/ qed-.
