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
include "ground/relocation/gr_map.ma".

(* DIVERGENCE CONDITION FOR GENERIC RELOCATION MAPS *************************)

(*** isdiv *)
coinductive gr_isd: predicate gr_map ≝
(*** isdiv_next *)
| gr_isd_next (f) (g):
  gr_isd f → ↑f = g → gr_isd g
.

interpretation
  "divergence condition (generic relocation maps)"
  'PredicateOmega f = (gr_isd f).

(* Basic inversions *********************************************************)

(*** isdiv_inv_gen *)
lemma gr_isd_inv_gen (g): 𝛀❪g❫ → ∃∃f. 𝛀❪f❫ & ↑f = g.
#g * -g
#f #g #Hf * /2 width=3 by ex2_intro/
qed-.

(* Advanced inversions ******************************************************)

(*** isdiv_inv_next *)
lemma gr_isd_inv_next (g): 𝛀❪g❫ → ∀f. ↑f = g → 𝛀❪f❫.
#g #H elim (gr_isd_inv_gen … H) -H
#f #Hf * -g #g #H >(eq_inv_gr_next_bi … H) -H //
qed-.

(*** isdiv_inv_push *)
lemma gr_isd_inv_push (g): 𝛀❪g❫ → ∀f. ⫯f = g → ⊥.
#g #H elim (gr_isd_inv_gen … H) -H
#f #Hf * -g #g #H elim (eq_inv_gr_push_next … H)
qed-.
