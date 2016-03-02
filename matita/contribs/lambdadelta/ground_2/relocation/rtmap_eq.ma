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

include "ground_2/notation/relations/funexteq_2.ma".
include "ground_2/relocation/rtmap.ma".

(* RELOCATION MAP ***********************************************************)

coinductive eq: relation rtmap ≝
| eq_push: ∀f1,f2,g1,g2. eq f1 f2 → ↑f1 = g1 → ↑f2 = g2 → eq g1 g2
| eq_next: ∀f1,f2,g1,g2. eq f1 f2 → ⫯f1 = g1 → ⫯f2 = g2 → eq g1 g2
.

interpretation "extensional equivalence (rtmap)"
   'FunExtEq f1 f2 = (eq f1 f2).

definition eq_repl (R:relation …) ≝
                   ∀f1,f2. f1 ≗ f2 → R f1 f2.

definition eq_repl_back (R:predicate …) ≝
                        ∀f1. R f1 → ∀f2. f1 ≗ f2 → R f2.

definition eq_repl_fwd (R:predicate …) ≝
                       ∀f1. R f1 → ∀f2. f2 ≗ f1 → R f2.

(* Basic properties *********************************************************)

let corec eq_refl: reflexive … eq ≝ ?.
#f cases (pn_split f) *
#g #Hg [ @(eq_push … Hg Hg) | @(eq_next … Hg Hg) ] -Hg //
qed.

let corec eq_sym: symmetric … eq ≝ ?.
#f1 #f2 * -f1 -f2
#f1 #f2 #g1 #g2 #Hf #H1 #H2
[ @(eq_push … H2 H1) | @(eq_next … H2 H1) ] -g2 -g1 /2 width=1 by/
qed-.

lemma eq_repl_sym: ∀R. eq_repl_back R → eq_repl_fwd R.
/3 width=3 by eq_sym/ qed-.

(* Basic inversion lemmas ***************************************************)

lemma eq_inv_px: ∀g1,g2. g1 ≗ g2 → ∀f1. ↑f1 = g1 →
                 ∃∃f2. f1 ≗ f2 & ↑f2 = g2.
#g1 #g2 * -g1 -g2
#f1 #f2 #g1 #g2 #Hf * * -g1 -g2
#x1 #H
[ lapply (injective_push … H) -H /2 width=3 by ex2_intro/
| elim (discr_push_next … H)
]
qed-.

lemma eq_inv_nx: ∀g1,g2. g1 ≗ g2 → ∀f1. ⫯f1 = g1 →
                 ∃∃f2. f1 ≗ f2 & ⫯f2 = g2.
#g1 #g2 * -g1 -g2
#f1 #f2 #g1 #g2 #Hf * * -g1 -g2
#x1 #H
[ elim (discr_next_push … H)
| lapply (injective_next … H) -H /2 width=3 by ex2_intro/
]
qed-.

lemma eq_inv_xp: ∀g1,g2. g1 ≗ g2 → ∀f2. ↑f2 = g2 →
                 ∃∃f1. f1 ≗ f2 & ↑f1 = g1.
#g1 #g2 * -g1 -g2
#f1 #f2 #g1 #g2 #Hf * * -g1 -g2
#x2 #H
[ lapply (injective_push … H) -H /2 width=3 by ex2_intro/
| elim (discr_push_next … H)
]
qed-.

lemma eq_inv_xn: ∀g1,g2. g1 ≗ g2 → ∀f2. ⫯f2 = g2 →
                 ∃∃f1. f1 ≗ f2 & ⫯f1 = g1.
#g1 #g2 * -g1 -g2
#f1 #f2 #g1 #g2 #Hf * * -g1 -g2
#x2 #H
[ elim (discr_next_push … H)
| lapply (injective_next … H) -H /2 width=3 by ex2_intro/
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma eq_inv_pp: ∀g1,g2. g1 ≗ g2 → ∀f1,f2. ↑f1 = g1 → ↑f2 = g2 → f1 ≗ f2.
#g1 #g2 #H #f1 #f2 #H1 elim (eq_inv_px … H … H1) -g1
#x2 #Hx2 * -g2
#H lapply (injective_push … H) -H //
qed-.

lemma eq_inv_nn: ∀g1,g2. g1 ≗ g2 → ∀f1,f2. ⫯f1 = g1 → ⫯f2 = g2 → f1 ≗ f2.
#g1 #g2 #H #f1 #f2 #H1 elim (eq_inv_nx … H … H1) -g1
#x2 #Hx2 * -g2
#H lapply (injective_next … H) -H //
qed-.

lemma eq_inv_pn: ∀g1,g2. g1 ≗ g2 → ∀f1,f2. ↑f1 = g1 → ⫯f2 = g2 → ⊥.
#g1 #g2 #H #f1 #f2 #H1 elim (eq_inv_px … H … H1) -g1
#x2 #Hx2 * -g2
#H elim (discr_next_push … H)
qed-.

lemma eq_inv_np: ∀g1,g2. g1 ≗ g2 → ∀f1,f2. ⫯f1 = g1 → ↑f2 = g2 → ⊥.
#g1 #g2 #H #f1 #f2 #H1 elim (eq_inv_nx … H … H1) -g1
#x2 #Hx2 * -g2
#H elim (discr_push_next … H)
qed-.

lemma eq_inv_gen: ∀f1,f2. f1 ≗ f2 →
                  (∃∃g1,g2. g1 ≗ g2 & ↑g1 = f1 & ↑g2 = f2) ∨
                  ∃∃g1,g2. g1 ≗ g2 & ⫯g1 = f1 & ⫯g2 = f2.
#f1 elim (pn_split f1) * #g1 #H1 #f2 #Hf
[ elim (eq_inv_px … Hf … H1) -Hf /3 width=5 by or_introl, ex3_2_intro/
| elim (eq_inv_nx … Hf … H1) -Hf /3 width=5 by or_intror, ex3_2_intro/
]
qed-.

(* Main properties **********************************************************)

let corec eq_trans: Transitive … eq ≝ ?.
#f1 #f * -f1 -f
#f1 #f #g1 #g #Hf1 #H1 #H #f2 #Hf2
[ cases (eq_inv_px … Hf2 … H) | cases (eq_inv_nx … Hf2 … H) ] -g
/3 width=5 by eq_push, eq_next/
qed-.

theorem eq_canc_sn: ∀f2. eq_repl_back (λf. f ≗ f2).
/3 width=3 by eq_trans, eq_sym/ qed-.

theorem eq_canc_dx: ∀f1. eq_repl_fwd (λf. f1 ≗ f).
/3 width=3 by eq_trans, eq_sym/ qed-.
