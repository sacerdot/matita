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
include "ground/relocation/gr_tl.ma".

(* RELATIONAL INTERSECTION FOR GENERIC RELOCATION MAPS **********************)

(*** sand *)
coinductive gr_sand: relation3 gr_map gr_map gr_map ≝
(*** sand_pp *)
| gr_sand_push_bi (f1) (f2) (f) (g1) (g2) (g):
  gr_sand f1 f2 f → ⫯f1 = g1 → ⫯f2 = g2 → ⫯f = g → gr_sand g1 g2 g
(*** sand_np *)
| gr_sand_next_push (f1) (f2) (f) (g1) (g2) (g):
  gr_sand f1 f2 f → ↑f1 = g1 → ⫯f2 = g2 → ⫯f = g → gr_sand g1 g2 g
(*** sand_pn *)
| gr_sand_push_next (f1) (f2) (f) (g1) (g2) (g):
  gr_sand f1 f2 f → ⫯f1 = g1 → ↑f2 = g2 → ⫯f = g → gr_sand g1 g2 g
(*** sand_nn *)
| gr_sand_next_bi (f1) (f2) (f) (g1) (g2) (g):
  gr_sand f1 f2 f → ↑f1 = g1 → ↑f2 = g2 → ↑f = g → gr_sand g1 g2 g
.

interpretation
  "relational intersection (generic relocation maps)"
  'RIntersection f1 f2 f = (gr_sand f1 f2 f).

(* Basic constructions ******************************************************)

(*** sand_refl *)
corec lemma gr_sand_idem:
            ∀f. f ⋒ f ≘ f.
#f cases (gr_map_split_tl f) #H
[ @(gr_sand_push_bi … H H H)
| @(gr_sand_next_bi … H H H)
] -H //
qed.

(*** sand_sym *)
corec lemma gr_sand_comm:
            ∀f1,f2,f. f1 ⋒ f2 ≘ f → f2 ⋒ f1 ≘ f.
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf * * * -g1 -g2 -g
[ @gr_sand_push_bi
| @gr_sand_push_next
| @gr_sand_next_push
| @gr_sand_next_bi
] /2 width=7 by/
qed-.

(* Basic inversions *********************************************************)

(*** sand_inv_ppx *)
lemma gr_sand_inv_push_bi:
      ∀g1,g2,g. g1 ⋒ g2 ≘ g → ∀f1,f2. ⫯f1 = g1 → ⫯f2 = g2 →
      ∃∃f. f1 ⋒ f2 ≘ f & ⫯f = g.
#g1 #g2 #g * -g1 -g2 -g
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #x1 #x2 #Hx1 #Hx2 destruct
try (>(eq_inv_gr_push_bi … Hx1) -x1) try (>(eq_inv_gr_next_bi … Hx1) -x1)
try elim (eq_inv_gr_push_next … Hx1) try elim (eq_inv_gr_next_push … Hx1)
try (>(eq_inv_gr_push_bi … Hx2) -x2) try (>(eq_inv_gr_next_bi … Hx2) -x2)
try elim (eq_inv_gr_push_next … Hx2) try elim (eq_inv_gr_next_push … Hx2)
/2 width=3 by ex2_intro/
qed-.

(*** sand_inv_npx *)
lemma gr_sand_inv_next_push:
      ∀g1,g2,g. g1 ⋒ g2 ≘ g → ∀f1,f2. ↑f1 = g1 → ⫯f2 = g2 →
      ∃∃f. f1 ⋒ f2 ≘ f & ⫯f = g.
#g1 #g2 #g * -g1 -g2 -g
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #x1 #x2 #Hx1 #Hx2 destruct
try (>(eq_inv_gr_push_bi … Hx1) -x1) try (>(eq_inv_gr_next_bi … Hx1) -x1)
try elim (eq_inv_gr_push_next … Hx1) try elim (eq_inv_gr_next_push … Hx1)
try (>(eq_inv_gr_push_bi … Hx2) -x2) try (>(eq_inv_gr_next_bi … Hx2) -x2)
try elim (eq_inv_gr_push_next … Hx2) try elim (eq_inv_gr_next_push … Hx2)
/2 width=3 by ex2_intro/
qed-.

(*** sand_inv_pnx *)
lemma gr_sand_inv_push_next:
      ∀g1,g2,g. g1 ⋒ g2 ≘ g → ∀f1,f2. ⫯f1 = g1 → ↑f2 = g2 →
      ∃∃f. f1 ⋒ f2 ≘ f & ⫯f = g.
#g1 #g2 #g * -g1 -g2 -g
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #x1 #x2 #Hx1 #Hx2 destruct
try (>(eq_inv_gr_push_bi … Hx1) -x1) try (>(eq_inv_gr_next_bi … Hx1) -x1)
try elim (eq_inv_gr_push_next … Hx1) try elim (eq_inv_gr_next_push … Hx1)
try (>(eq_inv_gr_push_bi … Hx2) -x2) try (>(eq_inv_gr_next_bi … Hx2) -x2)
try elim (eq_inv_gr_push_next … Hx2) try elim (eq_inv_gr_next_push … Hx2)
/2 width=3 by ex2_intro/
qed-.

(*** sand_inv_nnx *)
lemma gr_sand_inv_next_bi:
      ∀g1,g2,g. g1 ⋒ g2 ≘ g → ∀f1,f2. ↑f1 = g1 → ↑f2 = g2 →
      ∃∃f. f1 ⋒ f2 ≘ f & ↑f = g.
#g1 #g2 #g * -g1 -g2 -g
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #x1 #x2 #Hx1 #Hx2 destruct
try (>(eq_inv_gr_push_bi … Hx1) -x1) try (>(eq_inv_gr_next_bi … Hx1) -x1)
try elim (eq_inv_gr_push_next … Hx1) try elim (eq_inv_gr_next_push … Hx1)
try (>(eq_inv_gr_push_bi … Hx2) -x2) try (>(eq_inv_gr_next_bi … Hx2) -x2)
try elim (eq_inv_gr_push_next … Hx2) try elim (eq_inv_gr_next_push … Hx2)
/2 width=3 by ex2_intro/
qed-.
