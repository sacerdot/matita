(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.tcs.unibo.it                            *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "ground_2/relocation/rtmap_isid.ma".
include "ground_2/relocation/rtmap_isdiv.ma".

(* RELOCATION MAP ***********************************************************)

coinductive sle: relation rtmap ≝
| sle_push: ∀f1,f2,g1,g2. sle f1 f2 → ↑f1 = g1 → ↑f2 = g2 → sle g1 g2
| sle_next: ∀f1,f2,g1,g2. sle f1 f2 → ⫯f1 = g1 → ⫯f2 = g2 → sle g1 g2
| sle_weak: ∀f1,f2,g1,g2. sle f1 f2 → ↑f1 = g1 → ⫯f2 = g2 → sle g1 g2
.

interpretation "inclusion (rtmap)"
   'subseteq t1 t2 = (sle t1 t2).

(* Basic properties *********************************************************)

axiom sle_eq_repl_back1: ∀f2. eq_repl_back … (λf1. f1 ⊆ f2).

lemma sle_eq_repl_fwd1: ∀f2. eq_repl_fwd … (λf1. f1 ⊆ f2).
#f2 @eq_repl_sym /2 width=3 by sle_eq_repl_back1/
qed-.

axiom sle_eq_repl_back2: ∀f1. eq_repl_back … (λf2. f1 ⊆ f2).

lemma sle_eq_repl_fwd2: ∀f1. eq_repl_fwd … (λf2. f1 ⊆ f2).
#f1 @eq_repl_sym /2 width=3 by sle_eq_repl_back2/
qed-.

corec lemma sle_refl: ∀f. f ⊆ f.
#f cases (pn_split f) * #g #H
[ @(sle_push … H H) | @(sle_next … H H) ] -H //
qed.

lemma sle_refl_eq: ∀f1,f2. f1 ≗ f2 → f1 ⊆ f2.
/2 width=3 by sle_eq_repl_back2/ qed.

(* Basic inversion lemmas ***************************************************)

lemma sle_inv_xp: ∀g1,g2. g1 ⊆ g2 → ∀f2. ↑f2 = g2 →
                  ∃∃f1. f1 ⊆ f2 & ↑f1 = g1.
#g1 #g2 * -g1 -g2
#f1 #f2 #g1 #g2 #H #H1 #H2 #x2 #Hx2 destruct
[ lapply (injective_push … Hx2) -Hx2 /2 width=3 by ex2_intro/ ]
elim (discr_push_next … Hx2)
qed-.

lemma sle_inv_nx: ∀g1,g2. g1 ⊆ g2 → ∀f1. ⫯f1 = g1 →
                  ∃∃f2. f1 ⊆ f2 & ⫯f2 = g2.
#g1 #g2 * -g1 -g2
#f1 #f2 #g1 #g2 #H #H1 #H2 #x1 #Hx1 destruct
[2: lapply (injective_next … Hx1) -Hx1 /2 width=3 by ex2_intro/ ]
elim (discr_next_push … Hx1)
qed-.

lemma sle_inv_pn: ∀g1,g2. g1 ⊆ g2 → ∀f1,f2. ↑f1 = g1 → ⫯f2 = g2 → f1 ⊆ f2.
#g1 #g2 * -g1 -g2
#f1 #f2 #g1 #g2 #H #H1 #H2 #x1 #x2 #Hx1 #Hx2 destruct
[ elim (discr_next_push … Hx2)
| elim (discr_push_next … Hx1)
| lapply (injective_push … Hx1) -Hx1
  lapply (injective_next … Hx2) -Hx2 //
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma sle_inv_pp: ∀g1,g2. g1 ⊆ g2 → ∀f1,f2. ↑f1 = g1 → ↑f2 = g2 → f1 ⊆ f2.
#g1 #g2 #H #f1 #f2 #H1 #H2 elim (sle_inv_xp … H … H2) -g2
#x1 #H #Hx1 destruct lapply (injective_push … Hx1) -Hx1 //
qed-.

lemma sle_inv_nn: ∀g1,g2. g1 ⊆ g2 → ∀f1,f2.  ⫯f1 = g1 → ⫯f2 = g2 → f1 ⊆ f2.
#g1 #g2 #H #f1 #f2 #H1 #H2 elim (sle_inv_nx … H … H1) -g1
#x2 #H #Hx2 destruct lapply (injective_next … Hx2) -Hx2 //
qed-.

lemma sle_inv_px: ∀g1,g2. g1 ⊆ g2 → ∀f1. ↑f1 = g1 →
                  (∃∃f2. f1 ⊆ f2 & ↑f2 = g2) ∨ ∃∃f2. f1 ⊆ f2 & ⫯f2 = g2.
#g1 #g2 elim (pn_split g2) * #f2 #H2 #H #f1 #H1
[ lapply (sle_inv_pp … H … H1 H2) | lapply (sle_inv_pn … H … H1 H2) ] -H -H1
/3 width=3 by ex2_intro, or_introl, or_intror/
qed-.

lemma sle_inv_xn: ∀g1,g2. g1 ⊆ g2 → ∀f2. ⫯f2 = g2 →
                  (∃∃f1. f1 ⊆ f2 & ↑f1 = g1) ∨ ∃∃f1. f1 ⊆ f2 & ⫯f1 = g1.
#g1 #g2 elim (pn_split g1) * #f1 #H1 #H #f2 #H2
[ lapply (sle_inv_pn … H … H1 H2) | lapply (sle_inv_nn … H … H1 H2) ] -H -H2
/3 width=3 by ex2_intro, or_introl, or_intror/
qed-.

(* Main properties **********************************************************)

corec theorem sle_trans: Transitive … sle.
#f1 #f * -f1 -f
#f1 #f #g1 #g #Hf #H1 #H #g2 #H0
[ cases (sle_inv_px … H0 … H) * |*: cases (sle_inv_nx … H0 … H) ] -g
/3 width=5 by sle_push, sle_next, sle_weak/
qed-.

(* Properties with iteraded push ********************************************)

lemma sle_pushs: ∀f1,f2. f1 ⊆ f2 → ∀i. ↑*[i] f1 ⊆ ↑*[i] f2.
#f1 #f2 #Hf12 #i elim i -i /2 width=5 by sle_push/
qed.

(* Properties with tail *****************************************************)

lemma sle_px_tl: ∀g1,g2. g1 ⊆ g2 → ∀f1. ↑f1 = g1 → f1 ⊆ ⫱g2.
#g1 #g2 #H #f1 #H1 elim (sle_inv_px … H … H1) -H -H1 * //
qed.

lemma sle_xn_tl: ∀g1,g2. g1 ⊆ g2 → ∀f2. ⫯f2 = g2 → ⫱g1 ⊆ f2.
#g1 #g2 #H #f2 #H2 elim (sle_inv_xn … H … H2) -H -H2 * //
qed.

lemma sle_tl: ∀f1,f2. f1 ⊆ f2 → ⫱f1 ⊆ ⫱f2.
#f1 elim (pn_split f1) * #g1 #H1 #f2 #H
[ lapply (sle_px_tl … H … H1) -H //
| elim (sle_inv_nx … H … H1) -H //
]
qed.

(* Inversion lemmas with tail ***********************************************)

lemma sle_inv_tl_sn: ∀f1,f2. ⫱f1 ⊆ f2 → f1 ⊆ ⫯f2.
#f1 elim (pn_split f1) * #g1 #H destruct
/2 width=5 by sle_next, sle_weak/
qed-.

lemma sle_inv_tl_dx: ∀f1,f2. f1 ⊆ ⫱f2 → ↑f1 ⊆ f2.
#f1 #f2 elim (pn_split f2) * #g2 #H destruct
/2 width=5 by sle_push, sle_weak/
qed-.

(* Properties with isid *****************************************************)

corec lemma sle_isid_sn: ∀f1. 𝐈⦃f1⦄ → ∀f2. f1 ⊆ f2.
#f1 * -f1
#f1 #g1 #Hf1 #H1 #f2 cases (pn_split f2) *
/3 width=5 by sle_weak, sle_push/
qed.

(* Inversion lemmas with isid ***********************************************)

corec lemma sle_inv_isid_dx: ∀f1,f2. f1 ⊆ f2 → 𝐈⦃f2⦄ → 𝐈⦃f1⦄.
#f1 #f2 * -f1 -f2
#f1 #f2 #g1 #g2 #Hf * * #H
[2,3: elim (isid_inv_next … H) // ]
lapply (isid_inv_push … H ??) -H
/3 width=3 by isid_push/
qed-.

(* Properties with isdiv ****************************************************)

corec lemma sle_isdiv_dx: ∀f2. 𝛀⦃f2⦄ → ∀f1. f1 ⊆ f2.
#f2 * -f2
#f2 #g2 #Hf2 #H2 #f1 cases (pn_split f1) *
/3 width=5 by sle_weak, sle_next/
qed.

(* Inversion lemmas with isdiv **********************************************)

corec lemma sle_inv_isdiv_sn: ∀f1,f2. f1 ⊆ f2 → 𝛀⦃f1⦄ → 𝛀⦃f2⦄.
#f1 #f2 * -f1 -f2
#f1 #f2 #g1 #g2 #Hf * * #H
[1,3: elim (isdiv_inv_push … H) // ]
lapply (isdiv_inv_next … H ??) -H
/3 width=3 by isdiv_next/
qed-.
