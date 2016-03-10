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

(* Basic properties *********************************************************)

let corec sor_refl: ∀f. f ⋓ f ≡ f ≝ ?.
#f cases (pn_split f) * #g #H
[ @(sor_pp … H H H) | @(sor_nn … H H H) ] -H //
qed.

let corec sor_sym: ∀f1,f2,f. f1 ⋓ f2 ≡ f → f2 ⋓ f1 ≡ f ≝ ?.
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf * * * -g1 -g2 -g
[ @sor_pp | @sor_pn | @sor_np | @sor_nn ] /2 width=7 by/
qed-.
