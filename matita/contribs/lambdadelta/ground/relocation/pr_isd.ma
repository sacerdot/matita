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

include "ground/notation/relations/predicate_omega_1.ma".
include "ground/relocation/pr_map.ma".

(* DIVERGENCE CONDITION FOR PARTIAL RELOCATION MAPS *************************)

(*** isdiv *)
coinductive pr_isd: predicate pr_map ≝
(*** isdiv_next *)
| pr_isd_next (f) (g):
  pr_isd f → ↑f = g → pr_isd g
.

interpretation
  "divergence condition (partial relocation maps)"
  'PredicateOmega f = (pr_isd f).

(* Basic inversions *********************************************************)

(*** isdiv_inv_gen *)
lemma pr_isd_inv_gen (g): 𝛀❨g❩ → ∃∃f. 𝛀❨f❩ & ↑f = g.
#g * -g
#f #g #Hf * /2 width=3 by ex2_intro/
qed-.

(* Advanced inversions ******************************************************)

(*** isdiv_inv_next *)
lemma pr_isd_inv_next (g): 𝛀❨g❩ → ∀f. ↑f = g → 𝛀❨f❩.
#g #H elim (pr_isd_inv_gen … H) -H
#f #Hf * -g #g #H >(eq_inv_pr_next_bi … H) -H //
qed-.

(*** isdiv_inv_push *)
lemma pr_isd_inv_push (g): 𝛀❨g❩ → ∀f. ⫯f = g → ⊥.
#g #H elim (pr_isd_inv_gen … H) -H
#f #Hf * -g #g #H elim (eq_inv_pr_push_next … H)
qed-.
