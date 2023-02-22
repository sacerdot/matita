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

include "ground/notation/relations/rintersection_3.ma".
include "ground/relocation/pr_tl.ma".

(* RELATIONAL INTERSECTION FOR PARTIAL RELOCATION MAPS **********************)

(*** sand *)
coinductive pr_sand: relation3 pr_map pr_map pr_map ≝
(*** sand_pp *)
| pr_sand_push_bi (f1) (f2) (f) (g1) (g2) (g):
  pr_sand f1 f2 f → ⫯f1 = g1 → ⫯f2 = g2 → ⫯f = g → pr_sand g1 g2 g
(*** sand_np *)
| pr_sand_next_push (f1) (f2) (f) (g1) (g2) (g):
  pr_sand f1 f2 f → ↑f1 = g1 → ⫯f2 = g2 → ⫯f = g → pr_sand g1 g2 g
(*** sand_pn *)
| pr_sand_push_next (f1) (f2) (f) (g1) (g2) (g):
  pr_sand f1 f2 f → ⫯f1 = g1 → ↑f2 = g2 → ⫯f = g → pr_sand g1 g2 g
(*** sand_nn *)
| pr_sand_next_bi (f1) (f2) (f) (g1) (g2) (g):
  pr_sand f1 f2 f → ↑f1 = g1 → ↑f2 = g2 → ↑f = g → pr_sand g1 g2 g
.

interpretation
  "relational intersection (partial relocation maps)"
  'RIntersection f1 f2 f = (pr_sand f1 f2 f).

(* Basic constructions ******************************************************)

(*** sand_refl *)
corec lemma pr_sand_idem:
            ∀f. f ⋒ f ≘ f.
#f cases (pr_map_split_tl f) #H
[ @(pr_sand_push_bi … H H H)
| @(pr_sand_next_bi … H H H)
] -H //
qed.

(*** sand_sym *)
corec lemma pr_sand_comm:
            ∀f1,f2,f. f1 ⋒ f2 ≘ f → f2 ⋒ f1 ≘ f.
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf * * * -g1 -g2 -g
[ @pr_sand_push_bi
| @pr_sand_push_next
| @pr_sand_next_push
| @pr_sand_next_bi
] /2 width=7 by/
qed-.

(* Basic inversions *********************************************************)

(*** sand_inv_ppx *)
lemma pr_sand_inv_push_bi:
      ∀g1,g2,g. g1 ⋒ g2 ≘ g → ∀f1,f2. ⫯f1 = g1 → ⫯f2 = g2 →
      ∃∃f. f1 ⋒ f2 ≘ f & ⫯f = g.
#g1 #g2 #g * -g1 -g2 -g
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #x1 #x2 #Hx1 #Hx2 destruct
try (>(eq_inv_pr_push_bi … Hx1) -x1) try (>(eq_inv_pr_next_bi … Hx1) -x1)
try elim (eq_inv_pr_push_next … Hx1) try elim (eq_inv_pr_next_push … Hx1)
try (>(eq_inv_pr_push_bi … Hx2) -x2) try (>(eq_inv_pr_next_bi … Hx2) -x2)
try elim (eq_inv_pr_push_next … Hx2) try elim (eq_inv_pr_next_push … Hx2)
/2 width=3 by ex2_intro/
qed-.

(*** sand_inv_npx *)
lemma pr_sand_inv_next_push:
      ∀g1,g2,g. g1 ⋒ g2 ≘ g → ∀f1,f2. ↑f1 = g1 → ⫯f2 = g2 →
      ∃∃f. f1 ⋒ f2 ≘ f & ⫯f = g.
#g1 #g2 #g * -g1 -g2 -g
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #x1 #x2 #Hx1 #Hx2 destruct
try (>(eq_inv_pr_push_bi … Hx1) -x1) try (>(eq_inv_pr_next_bi … Hx1) -x1)
try elim (eq_inv_pr_push_next … Hx1) try elim (eq_inv_pr_next_push … Hx1)
try (>(eq_inv_pr_push_bi … Hx2) -x2) try (>(eq_inv_pr_next_bi … Hx2) -x2)
try elim (eq_inv_pr_push_next … Hx2) try elim (eq_inv_pr_next_push … Hx2)
/2 width=3 by ex2_intro/
qed-.

(*** sand_inv_pnx *)
lemma pr_sand_inv_push_next:
      ∀g1,g2,g. g1 ⋒ g2 ≘ g → ∀f1,f2. ⫯f1 = g1 → ↑f2 = g2 →
      ∃∃f. f1 ⋒ f2 ≘ f & ⫯f = g.
#g1 #g2 #g * -g1 -g2 -g
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #x1 #x2 #Hx1 #Hx2 destruct
try (>(eq_inv_pr_push_bi … Hx1) -x1) try (>(eq_inv_pr_next_bi … Hx1) -x1)
try elim (eq_inv_pr_push_next … Hx1) try elim (eq_inv_pr_next_push … Hx1)
try (>(eq_inv_pr_push_bi … Hx2) -x2) try (>(eq_inv_pr_next_bi … Hx2) -x2)
try elim (eq_inv_pr_push_next … Hx2) try elim (eq_inv_pr_next_push … Hx2)
/2 width=3 by ex2_intro/
qed-.

(*** sand_inv_nnx *)
lemma pr_sand_inv_next_bi:
      ∀g1,g2,g. g1 ⋒ g2 ≘ g → ∀f1,f2. ↑f1 = g1 → ↑f2 = g2 →
      ∃∃f. f1 ⋒ f2 ≘ f & ↑f = g.
#g1 #g2 #g * -g1 -g2 -g
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #x1 #x2 #Hx1 #Hx2 destruct
try (>(eq_inv_pr_push_bi … Hx1) -x1) try (>(eq_inv_pr_next_bi … Hx1) -x1)
try elim (eq_inv_pr_push_next … Hx1) try elim (eq_inv_pr_next_push … Hx1)
try (>(eq_inv_pr_push_bi … Hx2) -x2) try (>(eq_inv_pr_next_bi … Hx2) -x2)
try elim (eq_inv_pr_push_next … Hx2) try elim (eq_inv_pr_next_push … Hx2)
/2 width=3 by ex2_intro/
qed-.
