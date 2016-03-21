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

include "ground_2/notation/relations/runion_3.ma".
include "ground_2/relocation/rtmap_isfin.ma".
include "ground_2/relocation/rtmap_sle.ma".

coinductive sor: relation3 rtmap rtmap rtmap ≝
| sor_pp: ∀f1,f2,f,g1,g2,g. sor f1 f2 f → ↑f1 = g1 → ↑f2 = g2 → ↑f = g → sor g1 g2 g
| sor_np: ∀f1,f2,f,g1,g2,g. sor f1 f2 f → ⫯f1 = g1 → ↑f2 = g2 → ⫯f = g → sor g1 g2 g
| sor_pn: ∀f1,f2,f,g1,g2,g. sor f1 f2 f → ↑f1 = g1 → ⫯f2 = g2 → ⫯f = g → sor g1 g2 g
| sor_nn: ∀f1,f2,f,g1,g2,g. sor f1 f2 f → ⫯f1 = g1 → ⫯f2 = g2 → ⫯f = g → sor g1 g2 g
.

interpretation "union (rtmap)"
   'RUnion f1 f2 f = (sor f1 f2 f).

(* Basic inversion lemmas ***************************************************)

lemma sor_inv_ppx: ∀g1,g2,g. g1 ⋓ g2 ≡ g → ∀f1,f2. ↑f1 = g1 → ↑f2 = g2 →
                   ∃∃f. f1 ⋓ f2 ≡ f & ↑f = g.
#g1 #g2 #g * -g1 -g2 -g
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #x1 #x2 #Hx1 #Hx2 destruct
try (>(injective_push … Hx1) -x1) try (>(injective_next … Hx1) -x1)
try elim (discr_push_next … Hx1) try elim (discr_next_push … Hx1)
try (>(injective_push … Hx2) -x2) try (>(injective_next … Hx2) -x2)
try elim (discr_push_next … Hx2) try elim (discr_next_push … Hx2)
/2 width=3 by ex2_intro/
qed-.

lemma sor_inv_npx: ∀g1,g2,g. g1 ⋓ g2 ≡ g → ∀f1,f2. ⫯f1 = g1 → ↑f2 = g2 →
                   ∃∃f. f1 ⋓ f2 ≡ f & ⫯f = g.
#g1 #g2 #g * -g1 -g2 -g
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #x1 #x2 #Hx1 #Hx2 destruct
try (>(injective_push … Hx1) -x1) try (>(injective_next … Hx1) -x1)
try elim (discr_push_next … Hx1) try elim (discr_next_push … Hx1)
try (>(injective_push … Hx2) -x2) try (>(injective_next … Hx2) -x2)
try elim (discr_push_next … Hx2) try elim (discr_next_push … Hx2)
/2 width=3 by ex2_intro/
qed-.

lemma sor_inv_pnx: ∀g1,g2,g. g1 ⋓ g2 ≡ g → ∀f1,f2. ↑f1 = g1 → ⫯f2 = g2 →
                   ∃∃f. f1 ⋓ f2 ≡ f & ⫯f = g.
#g1 #g2 #g * -g1 -g2 -g
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #x1 #x2 #Hx1 #Hx2 destruct
try (>(injective_push … Hx1) -x1) try (>(injective_next … Hx1) -x1)
try elim (discr_push_next … Hx1) try elim (discr_next_push … Hx1)
try (>(injective_push … Hx2) -x2) try (>(injective_next … Hx2) -x2)
try elim (discr_push_next … Hx2) try elim (discr_next_push … Hx2)
/2 width=3 by ex2_intro/
qed-.

lemma sor_inv_nnx: ∀g1,g2,g. g1 ⋓ g2 ≡ g → ∀f1,f2. ⫯f1 = g1 → ⫯f2 = g2 →
                   ∃∃f. f1 ⋓ f2 ≡ f & ⫯f = g.
#g1 #g2 #g * -g1 -g2 -g
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #x1 #x2 #Hx1 #Hx2 destruct
try (>(injective_push … Hx1) -x1) try (>(injective_next … Hx1) -x1)
try elim (discr_push_next … Hx1) try elim (discr_next_push … Hx1)
try (>(injective_push … Hx2) -x2) try (>(injective_next … Hx2) -x2)
try elim (discr_push_next … Hx2) try elim (discr_next_push … Hx2)
/2 width=3 by ex2_intro/
qed-.

(* Main inversion lemmas ****************************************************)

corec theorem sor_mono: ∀f1,f2,x,y. f1 ⋓ f2 ≡ x → f1 ⋓ f2 ≡ y → x ≗ y.
#f1 #f2 #x #y * -f1 -f2 -x
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #H
[ cases (sor_inv_ppx … H … H1 H2)
| cases (sor_inv_npx … H … H1 H2)
| cases (sor_inv_pnx … H … H1 H2)
| cases (sor_inv_nnx … H … H1 H2)
] -g1 -g2
/3 width=5 by eq_push, eq_next/
qed-.

(* Basic properties *********************************************************)

corec lemma sor_eq_repl_back1: ∀f2,f. eq_repl_back … (λf1. f1 ⋓ f2 ≡ f).
#f2 #f #f1 * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #x #Hx
try cases (eq_inv_px … Hx … H1) try cases (eq_inv_nx … Hx … H1) -g1
/3 width=7 by sor_pp, sor_np, sor_pn, sor_nn/
qed-.

lemma sor_eq_repl_fwd1: ∀f2,f. eq_repl_fwd … (λf1. f1 ⋓ f2 ≡ f).
#f2 #f @eq_repl_sym /2 width=3 by sor_eq_repl_back1/
qed-.

corec lemma sor_eq_repl_back2: ∀f1,f. eq_repl_back … (λf2. f1 ⋓ f2 ≡ f).
#f1 #f #f2 * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf #H #H2 #H0 #x #Hx
try cases (eq_inv_px … Hx … H2) try cases (eq_inv_nx … Hx … H2) -g2
/3 width=7 by sor_pp, sor_np, sor_pn, sor_nn/
qed-.

lemma sor_eq_repl_fwd2: ∀f1,f. eq_repl_fwd … (λf2. f1 ⋓ f2 ≡ f).
#f1 #f @eq_repl_sym /2 width=3 by sor_eq_repl_back2/
qed-.

corec lemma sor_eq_repl_back3: ∀f1,f2. eq_repl_back … (λf. f1 ⋓ f2 ≡ f).
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf #H #H2 #H0 #x #Hx
try cases (eq_inv_px … Hx … H0) try cases (eq_inv_nx … Hx … H0) -g
/3 width=7 by sor_pp, sor_np, sor_pn, sor_nn/
qed-.

lemma sor_eq_repl_fwd3: ∀f1,f2. eq_repl_fwd … (λf. f1 ⋓ f2 ≡ f).
#f1 #f2 @eq_repl_sym /2 width=3 by sor_eq_repl_back3/
qed-.

corec lemma sor_refl: ∀f. f ⋓ f ≡ f.
#f cases (pn_split f) * #g #H
[ @(sor_pp … H H H) | @(sor_nn … H H H) ] -H //
qed.

corec lemma sor_sym: ∀f1,f2,f. f1 ⋓ f2 ≡ f → f2 ⋓ f1 ≡ f.
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf * * * -g1 -g2 -g
[ @sor_pp | @sor_pn | @sor_np | @sor_nn ] /2 width=7 by/
qed-.

(* Properies on identity ****************************************************)

corec lemma sor_isid_sn: ∀f1. 𝐈⦃f1⦄ → ∀f2. f1 ⋓ f2 ≡ f2.
#f1 * -f1
#f1 #g1 #Hf1 #H1 #f2 cases (pn_split f2) *
/3 width=7 by sor_pp, sor_pn/
qed.

corec lemma sor_isid_dx: ∀f2. 𝐈⦃f2⦄ → ∀f1. f1 ⋓ f2 ≡ f1.
#f2 * -f2
#f2 #g2 #Hf2 #H2 #f1 cases (pn_split f1) *
/3 width=7 by sor_pp, sor_np/
qed.

(* Properties on finite colength assignment *********************************)

lemma sor_fcla_ex: ∀f1,n1. 𝐂⦃f1⦄ ≡ n1 → ∀f2,n2. 𝐂⦃f2⦄ ≡ n2 →
                   ∃∃f,n. f1 ⋓ f2 ≡ f & 𝐂⦃f⦄ ≡ n & (n1 ∨ n2) ≤ n & n ≤ n1 + n2.
#f1 #n1 #Hf1 elim Hf1 -f1 -n1 /3 width=6 by sor_isid_sn, ex4_2_intro/
#f1 #n1 #Hf1 #IH #f2 #n2 * -f2 -n2 /3 width=6 by fcla_push, fcla_next, ex4_2_intro, sor_isid_dx/
#f2 #n2 #Hf2 elim (IH … Hf2) -IH -Hf2 -Hf1
[ /3 width=7 by fcla_push, sor_pp, ex4_2_intro/
| /3 width=7 by fcla_next, sor_pn, max_S2_le_S, le_S_S, ex4_2_intro/
| /3 width=7 by fcla_next, sor_np, max_S1_le_S, le_S_S, ex4_2_intro/
| /4 width=7 by fcla_next, sor_nn, le_S, le_S_S, ex4_2_intro/
]
qed-.

lemma sor_fcla: ∀f1,n1. 𝐂⦃f1⦄ ≡ n1 → ∀f2,n2. 𝐂⦃f2⦄ ≡ n2 → ∀f. f1 ⋓ f2 ≡ f →
                ∃∃n. 𝐂⦃f⦄ ≡ n & (n1 ∨ n2) ≤ n & n ≤ n1 + n2.
#f1 #n1 #Hf1 #f2 #n2 #Hf2 #f #Hf elim (sor_fcla_ex … Hf1 … Hf2) -Hf1 -Hf2
/4 width=6 by sor_mono, fcla_eq_repl_back, ex3_intro/
qed-.

(* Properties on test for finite colength ***********************************)

lemma sor_isfin_ex: ∀f1,f2. 𝐅⦃f1⦄ → 𝐅⦃f2⦄ → ∃∃f. f1 ⋓ f2 ≡ f & 𝐅⦃f⦄.
#f1 #f2 * #n1 #H1 * #n2 #H2 elim (sor_fcla_ex … H1 … H2) -H1 -H2
/3 width=4 by ex2_intro, ex_intro/
qed-.

lemma sor_isfin: ∀f1,f2. 𝐅⦃f1⦄ → 𝐅⦃f2⦄ → ∀f. f1 ⋓ f2 ≡ f → 𝐅⦃f⦄.
#f1 #f2 #Hf1 #Hf2 #f #Hf elim (sor_isfin_ex … Hf1 … Hf2) -Hf1 -Hf2
/3 width=6 by sor_mono, isfin_eq_repl_back/
qed-.
