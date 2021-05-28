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
include "ground/relocation/gr_fcla.ma".

(* FINITE COLENGTH CONDITION FOR GENERIC RELOCATION MAPS *)

(*** isfin *)
definition gr_isf: predicate gr_map ≝
           λf. ∃n. 𝐂❪f❫ ≘ n.

interpretation
  "finite colength condition (generic relocation maps)"
  'PredicateF f = (gr_isf f).

(* Basic eliminators ********************************************************)

(*** isfin_ind *)
lemma gr_isf_ind (Q:predicate …):
      (∀f.  𝐈❪f❫ → Q f) →
      (∀f. 𝐅❪f❫ → Q f → Q (⫯f)) →
      (∀f. 𝐅❪f❫ → Q f → Q (↑f)) →
      ∀f. 𝐅❪f❫ → Q f.
#Q #IH1 #IH2 #IH3 #f #H elim H -H
#n #H elim H -f -n /3 width=2 by ex_intro/
qed-.

(* Basic inversion lemmas ***************************************************)

(*** isfin_inv_push *)
lemma gr_isf_inv_push (g): 𝐅❪g❫ → ∀f. ⫯f = g → 𝐅❪f❫.
#g * /3 width=4 by gr_fcla_inv_push, ex_intro/
qed-.

(*** isfin_inv_next *)
lemma gr_isf_inv_next (g): 𝐅❪g❫ → ∀f. ↑f = g → 𝐅❪f❫.
#g * #n #H #f #H0 elim (gr_fcla_inv_next … H … H0) -g
/2 width=2 by ex_intro/
qed-.

(* Basic properties *********************************************************)

(*** isfin_isid *)
lemma gr_isf_isi (f): 𝐈❪f❫ → 𝐅❪f❫.
/3 width=2 by gr_fcla_isi, ex_intro/ qed.

(*** isfin_push *)
lemma gr_isf_push (f): 𝐅❪f❫ → 𝐅❪⫯f❫.
#f * /3 width=2 by gr_fcla_push, ex_intro/
qed.

(*** isfin_next *)
lemma gr_isf_next (f): 𝐅❪f❫ → 𝐅❪↑f❫.
#f * /3 width=2 by gr_fcla_next, ex_intro/
qed.
