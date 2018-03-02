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

(* Advanced inversion lemmas ************************************************)

lemma sor_inv_ppn: ∀g1,g2,g. g1 ⋓ g2 ≡ g →
                   ∀f1,f2,f. ↑f1 = g1 → ↑f2 = g2 → ⫯f = g → ⊥.
#g1 #g2 #g #H #f1 #f2 #f #H1 #H2 #H0
elim (sor_inv_ppx … H … H1 H2) -g1 -g2 #x #_ #H destruct
/2 width=3 by discr_push_next/
qed-.

lemma sor_inv_nxp: ∀g1,g2,g. g1 ⋓ g2 ≡ g →
                   ∀f1,f. ⫯f1 = g1 → ↑f = g → ⊥.
#g1 #g2 #g #H #f1 #f #H1 #H0
elim (pn_split g2) * #f2 #H2
[ elim (sor_inv_npx … H … H1 H2)
| elim (sor_inv_nnx … H … H1 H2)
] -g1 -g2 #x #_ #H destruct
/2 width=3 by discr_next_push/
qed-.

lemma sor_inv_xnp: ∀g1,g2,g. g1 ⋓ g2 ≡ g →
                   ∀f2,f. ⫯f2 = g2 → ↑f = g → ⊥.
#g1 #g2 #g #H #f2 #f #H2 #H0
elim (pn_split g1) * #f1 #H1
[ elim (sor_inv_pnx … H … H1 H2)
| elim (sor_inv_nnx … H … H1 H2)
] -g1 -g2 #x #_ #H destruct
/2 width=3 by discr_next_push/
qed-.

lemma sor_inv_ppp: ∀g1,g2,g. g1 ⋓ g2 ≡ g →
                   ∀f1,f2,f. ↑f1 = g1 → ↑f2 = g2 → ↑f = g → f1 ⋓ f2 ≡ f.
#g1 #g2 #g #H #f1 #f2 #f #H1 #H2 #H0
elim (sor_inv_ppx … H … H1 H2) -g1 -g2 #x #Hx #H destruct
<(injective_push … H) -f //
qed-.

lemma sor_inv_npn: ∀g1,g2,g. g1 ⋓ g2 ≡ g →
                   ∀f1,f2,f. ⫯f1 = g1 → ↑f2 = g2 → ⫯f = g → f1 ⋓ f2 ≡ f.
#g1 #g2 #g #H #f1 #f2 #f #H1 #H2 #H0
elim (sor_inv_npx … H … H1 H2) -g1 -g2 #x #Hx #H destruct
<(injective_next … H) -f //
qed-.

lemma sor_inv_pnn: ∀g1,g2,g. g1 ⋓ g2 ≡ g →
                   ∀f1,f2,f. ↑f1 = g1 → ⫯f2 = g2 → ⫯f = g → f1 ⋓ f2 ≡ f.
#g1 #g2 #g #H #f1 #f2 #f #H1 #H2 #H0
elim (sor_inv_pnx … H … H1 H2) -g1 -g2 #x #Hx #H destruct
<(injective_next … H) -f //
qed-.

lemma sor_inv_nnn: ∀g1,g2,g. g1 ⋓ g2 ≡ g →
                   ∀f1,f2,f. ⫯f1 = g1 → ⫯f2 = g2 → ⫯f = g → f1 ⋓ f2 ≡ f.
#g1 #g2 #g #H #f1 #f2 #f #H1 #H2 #H0
elim (sor_inv_nnx … H … H1 H2) -g1 -g2 #x #Hx #H destruct
<(injective_next … H) -f //
qed-.

lemma sor_inv_pxp: ∀g1,g2,g. g1 ⋓ g2 ≡ g →
                   ∀f1,f. ↑f1 = g1 → ↑f = g →
                   ∃∃f2. f1 ⋓ f2 ≡ f & ↑f2 = g2.
#g1 #g2 #g #H #f1 #f #H1 #H0
elim (pn_split g2) * #f2 #H2
[ /3 width=7 by sor_inv_ppp, ex2_intro/
| elim (sor_inv_xnp … H … H2 H0)
]
qed-.

lemma sor_inv_xpp: ∀g1,g2,g. g1 ⋓ g2 ≡ g →
                   ∀f2,f. ↑f2 = g2 → ↑f = g →
                   ∃∃f1. f1 ⋓ f2 ≡ f & ↑f1 = g1.
#g1 #g2 #g #H #f2 #f #H2 #H0
elim (pn_split g1) * #f1 #H1
[ /3 width=7 by sor_inv_ppp, ex2_intro/
| elim (sor_inv_nxp … H … H1 H0)
]
qed-.

lemma sor_inv_pxn: ∀g1,g2,g. g1 ⋓ g2 ≡ g →
                   ∀f1,f. ↑f1 = g1 → ⫯f = g →
                   ∃∃f2. f1 ⋓ f2 ≡ f & ⫯f2 = g2.
#g1 #g2 #g #H #f1 #f #H1 #H0
elim (pn_split g2) * #f2 #H2
[ elim (sor_inv_ppn … H … H1 H2 H0)
| /3 width=7 by sor_inv_pnn, ex2_intro/
]
qed-.

lemma sor_inv_xpn: ∀g1,g2,g. g1 ⋓ g2 ≡ g →
                   ∀f2,f. ↑f2 = g2 → ⫯f = g →
                   ∃∃f1. f1 ⋓ f2 ≡ f & ⫯f1 = g1.
#g1 #g2 #g #H #f2 #f #H2 #H0
elim (pn_split g1) * #f1 #H1
[ elim (sor_inv_ppn … H … H1 H2 H0)
| /3 width=7 by sor_inv_npn, ex2_intro/
]
qed-.

lemma sor_inv_xxp: ∀g1,g2,g. g1 ⋓ g2 ≡ g → ∀f. ↑f = g →
                   ∃∃f1,f2. f1 ⋓ f2 ≡ f & ↑f1 = g1 & ↑f2 = g2.
#g1 #g2 #g #H #f #H0
elim (pn_split g1) * #f1 #H1
[ elim (sor_inv_pxp … H … H1 H0) -g /2 width=5 by ex3_2_intro/
| elim (sor_inv_nxp … H … H1 H0)
]
qed-.

lemma sor_inv_nxn: ∀g1,g2,g. g1 ⋓ g2 ≡ g →
                   ∀f1,f. ⫯f1 = g1 → ⫯f = g →
                   (∃∃f2. f1 ⋓ f2 ≡ f & ↑f2 = g2) ∨
                   ∃∃f2. f1 ⋓ f2 ≡ f & ⫯f2 = g2.
#g1 #g2 elim (pn_split g2) *
/4 width=7 by sor_inv_npn, sor_inv_nnn, ex2_intro, or_intror, or_introl/
qed-.

lemma sor_inv_xnn: ∀g1,g2,g. g1 ⋓ g2 ≡ g →
                   ∀f2,f. ⫯f2 = g2 → ⫯f = g →
                   (∃∃f1. f1 ⋓ f2 ≡ f & ↑f1 = g1) ∨
                   ∃∃f1. f1 ⋓ f2 ≡ f & ⫯f1 = g1.
#g1 elim (pn_split g1) *
/4 width=7 by sor_inv_pnn, sor_inv_nnn, ex2_intro, or_intror, or_introl/
qed-.

lemma sor_inv_xxn: ∀g1,g2,g. g1 ⋓ g2 ≡ g → ∀f. ⫯f = g →
                   ∨∨ ∃∃f1,f2. f1 ⋓ f2 ≡ f & ⫯f1 = g1 & ↑f2 = g2
                    | ∃∃f1,f2. f1 ⋓ f2 ≡ f & ↑f1 = g1 & ⫯f2 = g2
                    | ∃∃f1,f2. f1 ⋓ f2 ≡ f & ⫯f1 = g1 & ⫯f2 = g2.
#g1 #g2 #g #H #f #H0
elim (pn_split g1) * #f1 #H1
[ elim (sor_inv_pxn … H … H1 H0) -g
  /3 width=5 by or3_intro1, ex3_2_intro/
| elim (sor_inv_nxn … H … H1 H0) -g *
  /3 width=5 by or3_intro0, or3_intro2, ex3_2_intro/
]
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

corec lemma sor_idem: ∀f. f ⋓ f ≡ f.
#f cases (pn_split f) * #g #H
[ @(sor_pp … H H H) | @(sor_nn … H H H) ] -H //
qed.

corec lemma sor_comm: ∀f1,f2,f. f1 ⋓ f2 ≡ f → f2 ⋓ f1 ≡ f.
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf * * * -g1 -g2 -g
[ @sor_pp | @sor_pn | @sor_np | @sor_nn ] /2 width=7 by/
qed-.

(* Properties with tail *****************************************************)

lemma sor_tl: ∀f1,f2,f. f1 ⋓ f2 ≡ f → ⫱f1 ⋓ ⫱f2 ≡ ⫱f.
#f1 cases (pn_split f1) * #g1 #H1
#f2 cases (pn_split f2) * #g2 #H2
#f #Hf
[ cases (sor_inv_ppx … Hf … H1 H2)
| cases (sor_inv_pnx … Hf … H1 H2)
| cases (sor_inv_npx … Hf … H1 H2)
| cases (sor_inv_nnx … Hf … H1 H2)
] -Hf #g #Hg #H destruct //
qed.

lemma sor_xxn_tl: ∀g1,g2,g. g1 ⋓ g2 ≡ g → ∀f. ⫯f = g →
                  (∃∃f1,f2. f1 ⋓ f2 ≡ f & ⫯f1 = g1 & ⫱g2 = f2) ∨
                  (∃∃f1,f2. f1 ⋓ f2 ≡ f & ⫱g1 = f1 & ⫯f2 = g2).
#g1 #g2 #g #H #f #H0 elim (sor_inv_xxn … H … H0) -H -H0 *
/3 width=5 by ex3_2_intro, or_introl, or_intror/
qed-.

lemma sor_xnx_tl: ∀g1,g2,g. g1 ⋓ g2 ≡ g → ∀f2. ⫯f2 = g2 →
                  ∃∃f1,f. f1 ⋓ f2 ≡ f & ⫱g1 = f1 & ⫯f = g.
#g1 elim (pn_split g1) * #f1 #H1 #g2 #g #H #f2 #H2
[ elim (sor_inv_pnx … H … H1 H2) | elim (sor_inv_nnx … H … H1 H2) ] -g2
/3 width=5 by ex3_2_intro/
qed-.

lemma sor_nxx_tl: ∀g1,g2,g. g1 ⋓ g2 ≡ g → ∀f1. ⫯f1 = g1 →
                  ∃∃f2,f. f1 ⋓ f2 ≡ f & ⫱g2 = f2 & ⫯f = g.
#g1 #g2 elim (pn_split g2) * #f2 #H2 #g #H #f1 #H1
[ elim (sor_inv_npx … H … H1 H2) | elim (sor_inv_nnx … H … H1 H2) ] -g1
/3 width=5 by ex3_2_intro/
qed-.

(* Properties with iterated tail ********************************************)

lemma sor_tls: ∀f1,f2,f. f1 ⋓ f2 ≡ f →
               ∀n. ⫱*[n]f1 ⋓ ⫱*[n]f2 ≡ ⫱*[n]f.
#f1 #f2 #f #Hf #n elim n -n /2 width=1 by sor_tl/
qed.

(* Properies with test for identity *****************************************)

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

lemma sor_isid: ∀f1,f2,f. 𝐈⦃f1⦄ → 𝐈⦃f2⦄ → 𝐈⦃f⦄ → f1 ⋓ f2 ≡ f.
/4 width=3 by sor_eq_repl_back2, sor_eq_repl_back1, isid_inv_eq_repl/ qed.

(* Inversion lemmas with tail ***********************************************)

lemma sor_inv_tl_sn: ∀f1,f2,f. ⫱f1 ⋓ f2 ≡ f → f1 ⋓ ⫯f2 ≡ ⫯f.
#f1 #f2 #f elim (pn_split f1) *
#g1 #H destruct /2 width=7 by sor_pn, sor_nn/
qed-.

lemma sor_inv_tl_dx: ∀f1,f2,f. f1 ⋓ ⫱f2 ≡ f → ⫯f1 ⋓ f2 ≡ ⫯f.
#f1 #f2 #f elim (pn_split f2) *
#g2 #H destruct /2 width=7 by sor_np, sor_nn/
qed-.

(* Inversion lemmas with test for identity **********************************)

lemma sor_isid_inv_sn: ∀f1,f2,f. f1 ⋓ f2 ≡ f → 𝐈⦃f1⦄ → f2 ≗ f.
/3 width=4 by sor_isid_sn, sor_mono/
qed-.

lemma sor_isid_inv_dx: ∀f1,f2,f. f1 ⋓ f2 ≡ f → 𝐈⦃f2⦄ → f1 ≗ f.
/3 width=4 by sor_isid_dx, sor_mono/
qed-.

corec lemma sor_fwd_isid1: ∀f1,f2,f. f1 ⋓ f2 ≡ f → 𝐈⦃f⦄ → 𝐈⦃f1⦄.
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H #Hg
[ /4 width=6 by isid_inv_push, isid_push/ ]
cases (isid_inv_next … Hg … H)
qed-.

corec lemma sor_fwd_isid2: ∀f1,f2,f. f1 ⋓ f2 ≡ f → 𝐈⦃f⦄ → 𝐈⦃f2⦄.
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H #Hg
[ /4 width=6 by isid_inv_push, isid_push/ ]
cases (isid_inv_next … Hg … H)
qed-.

lemma sor_inv_isid3: ∀f1,f2,f. f1 ⋓ f2 ≡ f → 𝐈⦃f⦄ → 𝐈⦃f1⦄ ∧ 𝐈⦃f2⦄.
/3 width=4 by sor_fwd_isid2, sor_fwd_isid1, conj/ qed-.

(* Properties with finite colength assignment *******************************)

lemma sor_fcla_ex: ∀f1,n1. 𝐂⦃f1⦄ ≡ n1 → ∀f2,n2. 𝐂⦃f2⦄ ≡ n2 →
                   ∃∃f,n. f1 ⋓ f2 ≡ f & 𝐂⦃f⦄ ≡ n & (n1 ∨ n2) ≤ n & n ≤ n1 + n2.
#f1 #n1 #Hf1 elim Hf1 -f1 -n1 /3 width=6 by sor_isid_sn, ex4_2_intro/
#f1 #n1 #Hf1 #IH #f2 #n2 * -f2 -n2 /3 width=6 by fcla_push, fcla_next, ex4_2_intro, sor_isid_dx/
#f2 #n2 #Hf2 elim (IH … Hf2) -IH -Hf2 -Hf1 [2,4: #f #n <plus_n_Sm ] (**) (* full auto fails *)
[ /3 width=7 by fcla_next, sor_pn, max_S2_le_S, le_S_S, ex4_2_intro/
| /4 width=7 by fcla_next, sor_nn, le_S, le_S_S, ex4_2_intro/
| /3 width=7 by fcla_push, sor_pp, ex4_2_intro/
| /3 width=7 by fcla_next, sor_np, max_S1_le_S, le_S_S, ex4_2_intro/
]
qed-.

lemma sor_fcla: ∀f1,n1. 𝐂⦃f1⦄ ≡ n1 → ∀f2,n2. 𝐂⦃f2⦄ ≡ n2 → ∀f. f1 ⋓ f2 ≡ f →
                ∃∃n. 𝐂⦃f⦄ ≡ n & (n1 ∨ n2) ≤ n & n ≤ n1 + n2.
#f1 #n1 #Hf1 #f2 #n2 #Hf2 #f #Hf elim (sor_fcla_ex … Hf1 … Hf2) -Hf1 -Hf2
/4 width=6 by sor_mono, fcla_eq_repl_back, ex3_intro/
qed-.

(* Forward lemmas with finite colength **************************************)

lemma sor_fwd_fcla_sn_ex: ∀f,n. 𝐂⦃f⦄ ≡ n → ∀f1,f2. f1 ⋓ f2 ≡ f →
                          ∃∃n1.  𝐂⦃f1⦄ ≡ n1 & n1 ≤ n.
#f #n #H elim H -f -n
[ /4 width=4 by sor_fwd_isid1, fcla_isid, ex2_intro/
| #f #n #_ #IH #f1 #f2 #H
  elim (sor_inv_xxp … H) -H [ |*: // ] #g1 #g2 #Hf #H1 #H2 destruct
  elim (IH … Hf) -f /3 width=3 by fcla_push, ex2_intro/
| #f #n #_ #IH #f1 #f2 #H
  elim (sor_inv_xxn … H) -H [1,3,4: * |*: // ] #g1 #g2 #Hf #H1 #H2 destruct
  elim (IH … Hf) -f /3 width=3 by fcla_push, fcla_next, le_S_S, le_S, ex2_intro/
]
qed-.

lemma sor_fwd_fcla_dx_ex: ∀f,n. 𝐂⦃f⦄ ≡ n → ∀f1,f2. f1 ⋓ f2 ≡ f →
                          ∃∃n2.  𝐂⦃f2⦄ ≡ n2 & n2 ≤ n.
/3 width=4 by sor_fwd_fcla_sn_ex, sor_comm/ qed-.

(* Properties with test for finite colength *********************************)

lemma sor_isfin_ex: ∀f1,f2. 𝐅⦃f1⦄ → 𝐅⦃f2⦄ → ∃∃f. f1 ⋓ f2 ≡ f & 𝐅⦃f⦄.
#f1 #f2 * #n1 #H1 * #n2 #H2 elim (sor_fcla_ex … H1 … H2) -H1 -H2
/3 width=4 by ex2_intro, ex_intro/
qed-.

lemma sor_isfin: ∀f1,f2. 𝐅⦃f1⦄ → 𝐅⦃f2⦄ → ∀f. f1 ⋓ f2 ≡ f → 𝐅⦃f⦄.
#f1 #f2 #Hf1 #Hf2 #f #Hf elim (sor_isfin_ex … Hf1 … Hf2) -Hf1 -Hf2
/3 width=6 by sor_mono, isfin_eq_repl_back/
qed-.

(* Forward lemmas with test for finite colength *****************************)

lemma sor_fwd_isfin_sn: ∀f. 𝐅⦃f⦄ → ∀f1,f2. f1 ⋓ f2 ≡ f → 𝐅⦃f1⦄.
#f * #n #Hf #f1 #f2 #H
elim (sor_fwd_fcla_sn_ex … Hf … H) -f -f2 /2 width=2 by ex_intro/
qed-.

lemma sor_fwd_isfin_dx: ∀f. 𝐅⦃f⦄ → ∀f1,f2. f1 ⋓ f2 ≡ f → 𝐅⦃f2⦄.
#f * #n #Hf #f1 #f2 #H
elim (sor_fwd_fcla_dx_ex … Hf … H) -f -f1 /2 width=2 by ex_intro/
qed-.

(* Inversion lemmas with test for finite colength ***************************)

lemma sor_inv_isfin3: ∀f1,f2,f. f1 ⋓ f2 ≡ f → 𝐅⦃f⦄ → 𝐅⦃f1⦄ ∧ 𝐅⦃f2⦄.
/3 width=4 by sor_fwd_isfin_dx, sor_fwd_isfin_sn, conj/ qed-.

(* Inversion lemmas with inclusion ******************************************)

corec lemma sor_inv_sle_sn: ∀f1,f2,f. f1 ⋓ f2 ≡ f → f1 ⊆ f.
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0
/3 width=5 by sle_push, sle_next, sle_weak/
qed-.

corec lemma sor_inv_sle_dx: ∀f1,f2,f. f1 ⋓ f2 ≡ f → f2 ⊆ f.
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0
/3 width=5 by sle_push, sle_next, sle_weak/
qed-.

lemma sor_inv_sle_sn_trans: ∀f1,f2,f. f1 ⋓ f2 ≡ f → ∀g. g ⊆ f1 → g ⊆ f.
/3 width=4 by sor_inv_sle_sn, sle_trans/ qed-.

lemma sor_inv_sle_dx_trans: ∀f1,f2,f. f1 ⋓ f2 ≡ f → ∀g. g ⊆ f2 → g ⊆ f.
/3 width=4 by sor_inv_sle_dx, sle_trans/ qed-.

axiom sor_inv_sle: ∀f1,f2,f. f1 ⋓ f2 ≡ f → ∀g. f1 ⊆ g → f2 ⊆ g → f ⊆ g.

(* Properties with inclusion ************************************************)

corec lemma sor_sle_dx: ∀f1,f2. f1 ⊆ f2 → f1 ⋓ f2 ≡ f2.
#f1 #f2 * -f1 -f2 /3 width=7 by sor_pp, sor_nn, sor_pn/
qed.

corec lemma sor_sle_sn: ∀f1,f2. f1 ⊆ f2 → f2 ⋓ f1 ≡ f2.
#f1 #f2 * -f1 -f2 /3 width=7 by sor_pp, sor_nn, sor_np/
qed.

(* Main properties **********************************************************)

axiom monotonic_sle_sor: ∀f1,g1. f1 ⊆ g1 → ∀f2,g2. f2 ⊆ g2 →
                         ∀f. f1 ⋓ f2 ≡ f → ∀g. g1 ⋓ g2 ≡ g → f ⊆ g.

axiom sor_assoc_dx: ∀f0,f3,f4. f0 ⋓ f3 ≡ f4 →
                    ∀f1,f2. f1 ⋓ f2 ≡ f0 →
                    ∀f. f2 ⋓ f3 ≡ f → f1 ⋓ f ≡ f4.

axiom sor_assoc_sn: ∀f1,f0,f4. f1 ⋓ f0 ≡ f4 →
                    ∀f2, f3. f2 ⋓ f3 ≡ f0 →
                    ∀f. f1 ⋓ f2 ≡ f → f ⋓ f3 ≡ f4.

lemma sor_comm_23: ∀f0,f1,f2,f3,f4,f.
                   f0⋓f4 ≡ f1 → f1⋓f2 ≡ f → f0⋓f2 ≡ f3 → f3⋓f4 ≡ f.
/4 width=6 by sor_comm, sor_assoc_dx/ qed-.

corec theorem sor_comm_23_idem: ∀f0,f1,f2. f0 ⋓ f1 ≡ f2 →
                                ∀f. f1 ⋓ f2 ≡ f → f1 ⋓ f0 ≡ f.
#f0 #f1 #f2 * -f0 -f1 -f2
#f0 #f1 #f2 #g0 #g1 #g2 #Hf2 #H0 #H1 #H2 #g #Hg
[ cases (sor_inv_ppx … Hg … H1 H2)
| cases (sor_inv_pnx … Hg … H1 H2)
| cases (sor_inv_nnx … Hg … H1 H2)
| cases (sor_inv_nnx … Hg … H1 H2)
] -g2 #f #Hf #H
/3 width=7 by sor_nn, sor_np, sor_pn, sor_pp/
qed-.

corec theorem sor_coll_dx: ∀f1,f2,f. f1 ⋓ f2 ≡ f → ∀g1,g2,g. g1 ⋓ g2 ≡ g →
                           ∀g0. g1 ⋓ g0 ≡ f1 → g2 ⋓ g0 ≡ f2 → g ⋓ g0 ≡ f.
#f1 #f2 #f cases (pn_split f) * #x #Hx #Hf #g1 #g2 #g #Hg #g0 #Hf1 #Hf2
[ cases (sor_inv_xxp … Hf … Hx) -Hf #x1 #x2 #Hf #Hx1 #Hx2
  cases (sor_inv_xxp … Hf1 … Hx1) -f1 #y1 #y0 #Hf1 #Hy1 #Hy0
  cases (sor_inv_xpp … Hf2 … Hy0 … Hx2) -f2 #y2 #Hf2 #Hy2
  cases (sor_inv_ppx … Hg … Hy1 Hy2) -g1 -g2 #y #Hg #Hy
  @(sor_pp … Hy Hy0 Hx) -g -g0 -f /2 width=8 by/
| cases (pn_split g) * #y #Hy
  [ cases (sor_inv_xxp … Hg … Hy) -Hg #y1 #y2 #Hg #Hy1 #Hy2
    cases (sor_xxn_tl … Hf … Hx) * #x1 #x2 #_ #Hx1 #Hx2
    [ cases (sor_inv_pxn … Hf1 … Hy1 Hx1) -g1 #y0 #Hf1 #Hy0
      cases (sor_inv_pnx … Hf2 … Hy2 Hy0) -g2 -x2 #x2 #Hf2 #Hx2
    | cases (sor_inv_pxn … Hf2 … Hy2 Hx2) -g2 #y0 #Hf2 #Hy0
      cases (sor_inv_pnx … Hf1 … Hy1 Hy0) -g1 -x1 #x1 #Hf1 #Hx1
    ]
    lapply (sor_inv_nnn … Hf … Hx1 Hx2 Hx) -f1 -f2 #Hf
    @(sor_pn … Hy Hy0 Hx) -g -g0 -f /2 width=8 by/
  | lapply (sor_tl … Hf) -Hf #Hf
    lapply (sor_tl … Hg) -Hg #Hg
    lapply (sor_tl … Hf1) -Hf1 #Hf1
    lapply (sor_tl … Hf2) -Hf2 #Hf2
    cases (pn_split g0) * #y0 #Hy0
    [ @(sor_np … Hy Hy0 Hx) /2 width=8 by/
    | @(sor_nn … Hy Hy0 Hx) /2 width=8 by/
    ]
  ]
]
qed-.

corec theorem sor_distr_dx: ∀g0,g1,g2,g. g1 ⋓ g2 ≡ g →
                            ∀f1,f2,f. g1 ⋓ g0 ≡ f1 → g2 ⋓ g0 ≡ f2 → g ⋓ g0 ≡ f →
                            f1 ⋓ f2 ≡ f.
#g0 cases (pn_split g0) * #y0 #H0 #g1 #g2 #g
[ * -g1 -g2 -g #y1 #y2 #y #g1 #g2 #g #Hy #Hy1 #Hy2 #Hy #f1 #f2 #f #Hf1 #Hf2 #Hf
  [ cases (sor_inv_ppx … Hf1 … Hy1 H0) -g1
    cases (sor_inv_ppx … Hf2 … Hy2 H0) -g2
    cases (sor_inv_ppx … Hf … Hy H0) -g
  | cases (sor_inv_npx … Hf1 … Hy1 H0) -g1
    cases (sor_inv_ppx … Hf2 … Hy2 H0) -g2
    cases (sor_inv_npx … Hf … Hy H0) -g
  | cases (sor_inv_ppx … Hf1 … Hy1 H0) -g1
    cases (sor_inv_npx … Hf2 … Hy2 H0) -g2
    cases (sor_inv_npx … Hf … Hy H0) -g
  | cases (sor_inv_npx … Hf1 … Hy1 H0) -g1
    cases (sor_inv_npx … Hf2 … Hy2 H0) -g2
    cases (sor_inv_npx … Hf … Hy H0) -g
  ] -g0 #y #Hy #H #y2 #Hy2 #H2 #y1 #Hy1 #H1
  /3 width=8 by sor_nn, sor_np, sor_pn, sor_pp/
| #H #f1 #f2 #f #Hf1 #Hf2 #Hf
  cases (sor_xnx_tl … Hf1 … H0) -Hf1
  cases (sor_xnx_tl … Hf2 … H0) -Hf2
  cases (sor_xnx_tl … Hf … H0) -Hf
  -g0 #y #x #Hx #Hy #H #y2 #x2 #Hx2 #Hy2 #H2 #y1 #x1 #Hx1 #Hy1 #H1
  /4 width=8 by sor_tl, sor_nn/
]
qed-.
