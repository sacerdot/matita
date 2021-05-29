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

include "ground/notation/relations/predicate_t_1.ma".
include "ground/relocation/gr_pat.ma".

(* TOTALITY CONDITION FOR GENERIC RELOCATION MAPS ***************************)

(*** istot *)
definition gr_ist: predicate gr_map ≝
           λf. ∀i. ∃j. @❪i,f❫ ≘ j.

interpretation
  "totality condition (generic relocation maps)"
  'PredicateT f = (gr_ist f).

(* Basic inversions *********************************************************)

(*** istot_inv_push *)
lemma gr_ist_inv_push (g): 𝐓❪g❫ → ∀f. ⫯f = g → 𝐓❪f❫.
#g #Hg #f #H #i elim (Hg (↑i)) -Hg
#j #Hg elim (gr_pat_inv_succ_push … Hg … H) -Hg -H /2 width=3 by ex_intro/
qed-.

(*** istot_inv_next *)
lemma gr_ist_inv_next (g): 𝐓❪g❫ → ∀f. ↑f = g → 𝐓❪f❫.
#g #Hg #f #H #i elim (Hg i) -Hg
#j #Hg elim (gr_pat_inv_next … Hg … H) -Hg -H /2 width=2 by ex_intro/
qed-.

(* Constructions with gr_tl *************************************************)

(*** istot_tl *)
lemma gr_ist_tl (f): 𝐓❪f❫ → 𝐓❪⫱f❫.
#f cases (gr_map_split_tl f) *
/2 width=3 by gr_ist_inv_next, gr_ist_inv_push/
qed.
