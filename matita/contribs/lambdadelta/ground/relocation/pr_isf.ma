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

include "ground/notation/relations/predicate_f_1.ma".
include "ground/relocation/pr_fcla.ma".

(* FINITE COLENGTH CONDITION FOR PARTIAL RELOCATION MAPS ********************)

(*** isfin *)
definition pr_isf: predicate pr_map ā
           Ī»f. ān. šāØfā© ā n.

interpretation
  "finite colength condition (partial relocation maps)"
  'PredicateF f = (pr_isf f).

(* Basic eliminations *******************************************************)

(*** isfin_ind *)
lemma pr_isf_ind (Q:predicate ā¦):
      (āf.  šāØfā© ā Q f) ā
      (āf. šāØfā© ā Q f ā Q (ā«Æf)) ā
      (āf. šāØfā© ā Q f ā Q (āf)) ā
      āf. šāØfā© ā Q f.
#Q #IH1 #IH2 #IH3 #f #H elim H -H
#n #H elim H -f -n /3 width=2 by ex_intro/
qed-.

(* Basic inversions *********************************************************)

(*** isfin_inv_push *)
lemma pr_isf_inv_push (g): šāØgā© ā āf. ā«Æf = g ā šāØfā©.
#g * /3 width=4 by pr_fcla_inv_push, ex_intro/
qed-.

(*** isfin_inv_next *)
lemma pr_isf_inv_next (g): šāØgā© ā āf. āf = g ā šāØfā©.
#g * #n #H #f #H0 elim (pr_fcla_inv_next ā¦ H ā¦ H0) -g
/2 width=2 by ex_intro/
qed-.

(* Basic constructions ******************************************************)

(*** isfin_isid *)
lemma pr_isf_isi (f): šāØfā© ā šāØfā©.
/3 width=2 by pr_fcla_isi, ex_intro/ qed.

(*** isfin_push *)
lemma pr_isf_push (f): šāØfā© ā šāØā«Æfā©.
#f * /3 width=2 by pr_fcla_push, ex_intro/
qed.

(*** isfin_next *)
lemma pr_isf_next (f): šāØfā© ā šāØāfā©.
#f * /3 width=2 by pr_fcla_next, ex_intro/
qed.
