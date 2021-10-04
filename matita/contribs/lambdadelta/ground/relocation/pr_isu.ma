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
inductive pr_isu: predicate pr_map ≝
(*** isuni_isid *)
| pr_isu_isi (f): 𝐈❪f❫ → pr_isu f
(*** isuni_next *)
| pr_isu_next (f): pr_isu f → ∀g. ↑f = g → pr_isu g
.

interpretation
  "uniformity condition (partial relocation maps)"
  'PredicateU f = (pr_isu f).

(* Basic inversions *********************************************************)

(*** isuni_inv_push *)
lemma pr_isu_inv_push (g): 𝐔❪g❫ → ∀f. ⫯f = g → 𝐈❪f❫.
#g * -g
[ /2 width=3 by pr_isi_inv_push/
| #f #_ #g #H #x #Hx destruct
  elim (eq_inv_pr_push_next … Hx)
]
qed-.

(*** isuni_inv_next *)
lemma pr_isu_inv_next (g): 𝐔❪g❫ → ∀f. ↑f = g → 𝐔❪f❫.
#g * -g #f #Hf
[ #x #Hx elim (pr_isi_inv_next … Hf … Hx)
| #g #H #x #Hx destruct
  >(eq_inv_pr_next_bi … Hx) -x //
]
qed-.

(* Basic destructions *******************************************************)

(*** isuni_fwd_push *)
lemma pr_isu_fwd_push (g): 𝐔❪g❫ → ∀f. ⫯f = g → 𝐔❪f❫.
/3 width=3 by pr_isu_inv_push, pr_isu_isi/ qed-.
