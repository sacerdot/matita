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
include "ground/relocation/gr_map.ma".

(* IDENTITY CONDITION FOR GENERIC RELOCATION MAPS ***********************************************************)

(*** isid *)
coinductive gr_isi: predicate gr_map ≝
(*** isid_push *)
| gr_isi_push (f) (g):
  gr_isi f → ⫯f = g → gr_isi g
.

interpretation
  "identity condition (generic relocation maps)"
  'PredicateI f = (gr_isi f).

(* Basic inversion lemmas ***************************************************)

(*** isid_inv_gen *)
lemma gr_isi_inv_gen (g): 𝐈❪g❫ → ∃∃f. 𝐈❪f❫ & ⫯f = g.
#g * -g
#f #g #Hf /2 width=3 by ex2_intro/
qed-.

(* Advanced inversion lemmas ************************************************)

(*** isid_inv_push *)
lemma gr_isi_inv_push (g): 𝐈❪g❫ → ∀f. ⫯f = g → 𝐈❪f❫.
#g #H
elim (gr_isi_inv_gen … H) -H #f #Hf
* -g #g #H
>(eq_inv_gr_push_bi … H) -H //
qed-.

(*** isid_inv_next *)
lemma gr_isi_inv_next (g): 𝐈❪g❫ → ∀f. ↑f = g → ⊥.
#g #H
elim (gr_isi_inv_gen … H) -H #f #Hf
* -g #g #H elim (eq_inv_gr_next_push … H)
qed-.
