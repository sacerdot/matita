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
include "ground/relocation/rtmap_sle.ma".

coinductive sand: relation3 rtmap rtmap rtmap ≝
| sand_pp: ∀f1,f2,f,g1,g2,g. sand f1 f2 f → ⫯f1 = g1 → ⫯f2 = g2 → ⫯f = g → sand g1 g2 g
| sand_np: ∀f1,f2,f,g1,g2,g. sand f1 f2 f → ↑f1 = g1 → ⫯f2 = g2 → ⫯f = g → sand g1 g2 g
| sand_pn: ∀f1,f2,f,g1,g2,g. sand f1 f2 f → ⫯f1 = g1 → ↑f2 = g2 → ⫯f = g → sand g1 g2 g
| sand_nn: ∀f1,f2,f,g1,g2,g. sand f1 f2 f → ↑f1 = g1 → ↑f2 = g2 → ↑f = g → sand g1 g2 g
.

interpretation "intersection (rtmap)"
   'RIntersection f1 f2 f = (sand f1 f2 f).

(* Basic inversion lemmas ***************************************************)

lemma sand_inv_ppx: ∀g1,g2,g. g1 ⋒ g2 ≘ g → ∀f1,f2. ⫯f1 = g1 → ⫯f2 = g2 →
                    ∃∃f. f1 ⋒ f2 ≘ f & ⫯f = g.
#g1 #g2 #g * -g1 -g2 -g
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #x1 #x2 #Hx1 #Hx2 destruct
try (>(injective_push … Hx1) -x1) try (>(injective_next … Hx1) -x1)
try elim (discr_push_next … Hx1) try elim (discr_next_push … Hx1)
try (>(injective_push … Hx2) -x2) try (>(injective_next … Hx2) -x2)
try elim (discr_push_next … Hx2) try elim (discr_next_push … Hx2)
/2 width=3 by ex2_intro/
qed-.

lemma sand_inv_npx: ∀g1,g2,g. g1 ⋒ g2 ≘ g → ∀f1,f2. ↑f1 = g1 → ⫯f2 = g2 →
                    ∃∃f. f1 ⋒ f2 ≘ f & ⫯f = g.
#g1 #g2 #g * -g1 -g2 -g
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #x1 #x2 #Hx1 #Hx2 destruct
try (>(injective_push … Hx1) -x1) try (>(injective_next … Hx1) -x1)
try elim (discr_push_next … Hx1) try elim (discr_next_push … Hx1)
try (>(injective_push … Hx2) -x2) try (>(injective_next … Hx2) -x2)
try elim (discr_push_next … Hx2) try elim (discr_next_push … Hx2)
/2 width=3 by ex2_intro/
qed-.

lemma sand_inv_pnx: ∀g1,g2,g. g1 ⋒ g2 ≘ g → ∀f1,f2. ⫯f1 = g1 → ↑f2 = g2 →
                    ∃∃f. f1 ⋒ f2 ≘ f & ⫯f = g.
#g1 #g2 #g * -g1 -g2 -g
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #x1 #x2 #Hx1 #Hx2 destruct
try (>(injective_push … Hx1) -x1) try (>(injective_next … Hx1) -x1)
try elim (discr_push_next … Hx1) try elim (discr_next_push … Hx1)
try (>(injective_push … Hx2) -x2) try (>(injective_next … Hx2) -x2)
try elim (discr_push_next … Hx2) try elim (discr_next_push … Hx2)
/2 width=3 by ex2_intro/
qed-.

lemma sand_inv_nnx: ∀g1,g2,g. g1 ⋒ g2 ≘ g → ∀f1,f2. ↑f1 = g1 → ↑f2 = g2 →
                    ∃∃f. f1 ⋒ f2 ≘ f & ↑f = g.
#g1 #g2 #g * -g1 -g2 -g
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #x1 #x2 #Hx1 #Hx2 destruct
try (>(injective_push … Hx1) -x1) try (>(injective_next … Hx1) -x1)
try elim (discr_push_next … Hx1) try elim (discr_next_push … Hx1)
try (>(injective_push … Hx2) -x2) try (>(injective_next … Hx2) -x2)
try elim (discr_push_next … Hx2) try elim (discr_next_push … Hx2)
/2 width=3 by ex2_intro/
qed-.

(* Basic properties *********************************************************)

corec lemma sand_eq_repl_back1: ∀f2,f. eq_repl_back … (λf1. f1 ⋒ f2 ≘ f).
#f2 #f #f1 * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #x #Hx
try cases (eq_inv_px … Hx … H1) try cases (eq_inv_nx … Hx … H1) -g1
/3 width=7 by sand_pp, sand_np, sand_pn, sand_nn/
qed-.

lemma sand_eq_repl_fwd1: ∀f2,f. eq_repl_fwd … (λf1. f1 ⋒ f2 ≘ f).
#f2 #f @eq_repl_sym /2 width=3 by sand_eq_repl_back1/
qed-.

corec lemma sand_eq_repl_back2: ∀f1,f. eq_repl_back … (λf2. f1 ⋒ f2 ≘ f).
#f1 #f #f2 * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf #H #H2 #H0 #x #Hx
try cases (eq_inv_px … Hx … H2) try cases (eq_inv_nx … Hx … H2) -g2
/3 width=7 by sand_pp, sand_np, sand_pn, sand_nn/
qed-.

lemma sand_eq_repl_fwd2: ∀f1,f. eq_repl_fwd … (λf2. f1 ⋒ f2 ≘ f).
#f1 #f @eq_repl_sym /2 width=3 by sand_eq_repl_back2/
qed-.

corec lemma sand_eq_repl_back3: ∀f1,f2. eq_repl_back … (λf. f1 ⋒ f2 ≘ f).
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf #H #H2 #H0 #x #Hx
try cases (eq_inv_px … Hx … H0) try cases (eq_inv_nx … Hx … H0) -g
/3 width=7 by sand_pp, sand_np, sand_pn, sand_nn/
qed-.

lemma sand_eq_repl_fwd3: ∀f1,f2. eq_repl_fwd … (λf. f1 ⋒ f2 ≘ f).
#f1 #f2 @eq_repl_sym /2 width=3 by sand_eq_repl_back3/
qed-.

corec lemma sand_refl: ∀f. f ⋒ f ≘ f.
#f cases (pn_split f) * #g #H
[ @(sand_pp … H H H) | @(sand_nn … H H H) ] -H //
qed.

corec lemma sand_sym: ∀f1,f2,f. f1 ⋒ f2 ≘ f → f2 ⋒ f1 ≘ f.
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf * * * -g1 -g2 -g
[ @sand_pp | @sand_pn | @sand_np | @sand_nn ] /2 width=7 by/
qed-.
