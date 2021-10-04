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
definition pr_isf: predicate pr_map ≝
           λf. ∃n. 𝐂❪f❫ ≘ n.

interpretation
  "finite colength condition (partial relocation maps)"
  'PredicateF f = (pr_isf f).

(* Basic eliminations *******************************************************)

(*** isfin_ind *)
lemma pr_isf_ind (Q:predicate …):
      (∀f.  𝐈❪f❫ → Q f) →
      (∀f. 𝐅❪f❫ → Q f → Q (⫯f)) →
      (∀f. 𝐅❪f❫ → Q f → Q (↑f)) →
      ∀f. 𝐅❪f❫ → Q f.
#Q #IH1 #IH2 #IH3 #f #H elim H -H
#n #H elim H -f -n /3 width=2 by ex_intro/
qed-.

(* Basic inversions *********************************************************)

(*** isfin_inv_push *)
lemma pr_isf_inv_push (g): 𝐅❪g❫ → ∀f. ⫯f = g → 𝐅❪f❫.
#g * /3 width=4 by pr_fcla_inv_push, ex_intro/
qed-.

(*** isfin_inv_next *)
lemma pr_isf_inv_next (g): 𝐅❪g❫ → ∀f. ↑f = g → 𝐅❪f❫.
#g * #n #H #f #H0 elim (pr_fcla_inv_next … H … H0) -g
/2 width=2 by ex_intro/
qed-.

(* Basic constructions ******************************************************)

(*** isfin_isid *)
lemma pr_isf_isi (f): 𝐈❪f❫ → 𝐅❪f❫.
/3 width=2 by pr_fcla_isi, ex_intro/ qed.

(*** isfin_push *)
lemma pr_isf_push (f): 𝐅❪f❫ → 𝐅❪⫯f❫.
#f * /3 width=2 by pr_fcla_push, ex_intro/
qed.

(*** isfin_next *)
lemma pr_isf_next (f): 𝐅❪f❫ → 𝐅❪↑f❫.
#f * /3 width=2 by pr_fcla_next, ex_intro/
qed.
