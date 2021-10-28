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
include "ground/relocation/pr_pat.ma".

(* TOTALITY CONDITION FOR PARTIAL RELOCATION MAPS ***************************)

(*** istot *)
definition pr_ist: predicate pr_map ≝
           λf. ∀i. ∃j. @❪i,f❫ ≘ j.

interpretation
  "totality condition (partial relocation maps)"
  'PredicateT f = (pr_ist f).

(* Basic inversions *********************************************************)

(*** istot_inv_push *)
lemma pr_ist_inv_push (g): 𝐓❪g❫ → ∀f. ⫯f = g → 𝐓❪f❫.
#g #Hg #f #H #i elim (Hg (↑i)) -Hg
#j #Hg elim (pr_pat_inv_succ_push … Hg … H) -Hg -H /2 width=3 by ex_intro/
qed-.

(*** istot_inv_next *)
lemma pr_ist_inv_next (g): 𝐓❪g❫ → ∀f. ↑f = g → 𝐓❪f❫.
#g #Hg #f #H #i elim (Hg i) -Hg
#j #Hg elim (pr_pat_inv_next … Hg … H) -Hg -H /2 width=2 by ex_intro/
qed-.

(* Basic constructions ******************************************************)

lemma pr_ist_push (f): 𝐓❪f❫ → 𝐓❪⫯f❫.
#f #Hf *
[ /3 width=2 by pr_pat_refl, ex_intro/
| #i elim (Hf i) -Hf /3 width=8 by pr_pat_push, ex_intro/
]
qed.

lemma pr_ist_next (f): 𝐓❪f❫ → 𝐓❪↑f❫.
#f #Hf #i elim (Hf i) -Hf
/3 width=6 by pr_pat_next, ex_intro/
qed.

(* Constructions with pr_tl *************************************************)

(*** istot_tl *)
lemma pr_ist_tl (f): 𝐓❪f❫ → 𝐓❪⫰f❫.
#f cases (pr_map_split_tl f) *
/2 width=3 by pr_ist_inv_next, pr_ist_inv_push/
qed.
