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
include "ground/relocation/gr_isi.ma".

(* UNIFORMITY CONDITION FOR GENERIC RELOCATION MAPS ***********************************************************)

(*** isuni *)
inductive gr_isu: predicate gr_map ≝
(*** isuni_isid *)
| gr_isu_isi (f): 𝐈❪f❫ → gr_isu f
(*** isuni_next *)
| gr_isu_next (f): gr_isu f → ∀g. ↑f = g → gr_isu g
.

interpretation
  "uniformity condition (generic relocation maps)"
  'PredicateU f = (gr_isu f).

(* Basic inversion lemmas ***************************************************)

(*** isuni_inv_push *)
lemma gr_isu_inv_push (g): 𝐔❪g❫ → ∀f. ⫯f = g → 𝐈❪f❫.
#g * -g
[ /2 width=3 by gr_isi_inv_push/
| #f #_ #g #H #x #Hx destruct
  elim (eq_inv_gr_push_next … Hx)
]
qed-.

(*** isuni_inv_next *)
lemma gr_isu_inv_next (g): 𝐔❪g❫ → ∀f. ↑f = g → 𝐔❪f❫.
#g * -g #f #Hf
[ #x #Hx elim (gr_isi_inv_next … Hf … Hx)
| #g #H #x #Hx destruct
  >(eq_inv_gr_next_bi … Hx) -x //
]
qed-.

(* Basic forward lemmas *****************************************************)

(*** isuni_fwd_push *)
lemma gr_isu_fwd_push (g): 𝐔❪g❫ → ∀f. ⫯f = g → 𝐔❪f❫.
/3 width=3 by gr_isu_inv_push, gr_isu_isi/ qed-.
