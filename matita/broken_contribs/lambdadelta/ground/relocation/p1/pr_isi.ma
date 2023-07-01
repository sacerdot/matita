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

include "ground/notation/relations/predicate_i_1.ma".
include "ground/relocation/p1/pr_map.ma".

(* IDENTITY CONDITION FOR PARTIAL RELOCATION MAPS ***************************)

(*** isid *)
coinductive pr_isi: predicate pr_map ≝
(*** isid_push *)
| pr_isi_push (f) (g):
  pr_isi f → ⫯f = g → pr_isi g
.

interpretation
  "identity condition (partial relocation maps)"
  'PredicateI f = (pr_isi f).

(* Basic inversions *********************************************************)

(*** isid_inv_gen *)
lemma pr_isi_inv_gen (g): 𝐈❨g❩ → ∃∃f. 𝐈❨f❩ & ⫯f = g.
#g * -g
#f #g #Hf /2 width=3 by ex2_intro/
qed-.

(* Advanced inversions ******************************************************)

(*** isid_inv_push *)
lemma pr_isi_inv_push (g): 𝐈❨g❩ → ∀f. ⫯f = g → 𝐈❨f❩.
#g #H
elim (pr_isi_inv_gen … H) -H #f #Hf
* -g #g #H
>(eq_inv_pr_push_bi … H) -H //
qed-.

(*** isid_inv_next *)
lemma pr_isi_inv_next (g): 𝐈❨g❩ → ∀f. ↑f = g → ⊥.
#g #H
elim (pr_isi_inv_gen … H) -H #f #Hf
* -g #g #H elim (eq_inv_pr_next_push … H)
qed-.
