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

include "ground_2/notation/relations/parallel_2.ma".
include "ground_2/relocation/rtmap_isid.ma".

(* RELOCATION MAP ***********************************************************)

coinductive sdj: relation rtmap ≝
| sdj_pp: ∀f1,f2,g1,g2. sdj f1 f2 → ⫯f1 = g1 → ⫯f2 = g2 → sdj g1 g2
| sdj_np: ∀f1,f2,g1,g2. sdj f1 f2 → ↑f1 = g1 → ⫯f2 = g2 → sdj g1 g2
| sdj_pn: ∀f1,f2,g1,g2. sdj f1 f2 → ⫯f1 = g1 → ↑f2 = g2 → sdj g1 g2
.

interpretation "disjointness (rtmap)"
   'Parallel f1 f2 = (sdj f1 f2).

(* Basic properties *********************************************************)

axiom sdj_eq_repl_back1: ∀f2. eq_repl_back … (λf1. f1 ∥ f2).

lemma sdj_eq_repl_fwd1: ∀f2. eq_repl_fwd … (λf1. f1 ∥ f2).
#f2 @eq_repl_sym /2 width=3 by sdj_eq_repl_back1/
qed-.

axiom sdj_eq_repl_back2: ∀f1. eq_repl_back … (λf2. f1 ∥ f2).

lemma sdj_eq_repl_fwd2: ∀f1. eq_repl_fwd … (λf2. f1 ∥ f2).
#f1 @eq_repl_sym /2 width=3 by sdj_eq_repl_back2/
qed-.

corec lemma sdj_sym: symmetric … sdj.
#f1 #f2 * -f1 -f2
#f1 #f2 #g1 #g2 #Hf #H1 #H2
[ @(sdj_pp … H2 H1) | @(sdj_pn … H2 H1) | @(sdj_np … H2 H1) ] -g2 -g1
/2 width=1 by/
qed-.

(* Basic inversion lemmas ***************************************************)

lemma sdj_inv_pp: ∀g1,g2. g1 ∥ g2 → ∀f1,f2. ⫯f1 = g1 → ⫯f2 = g2 → f1 ∥ f2.
#g1 #g2 * -g1 -g2
#f1 #f2 #g1 #g2 #H #H1 #H2 #x1 #x2 #Hx1 #Hx2 destruct
[ lapply (injective_push … Hx1) -Hx1
  lapply (injective_push … Hx2) -Hx2 //
| elim (discr_push_next … Hx1)
| elim (discr_push_next … Hx2)
]
qed-.

lemma sdj_inv_np: ∀g1,g2. g1 ∥ g2 → ∀f1,f2. ↑f1 = g1 → ⫯f2 = g2 → f1 ∥ f2.
#g1 #g2 * -g1 -g2
#f1 #f2 #g1 #g2 #H #H1 #H2 #x1 #x2 #Hx1 #Hx2 destruct
[ elim (discr_next_push … Hx1)
| lapply (injective_next … Hx1) -Hx1
  lapply (injective_push … Hx2) -Hx2 //
| elim (discr_push_next … Hx2)
]
qed-.

lemma sdj_inv_pn: ∀g1,g2. g1 ∥ g2 → ∀f1,f2. ⫯f1 = g1 → ↑f2 = g2 → f1 ∥ f2.
#g1 #g2 * -g1 -g2
#f1 #f2 #g1 #g2 #H #H1 #H2 #x1 #x2 #Hx1 #Hx2 destruct
[ elim (discr_next_push … Hx2)
| elim (discr_push_next … Hx1)
| lapply (injective_push … Hx1) -Hx1
  lapply (injective_next … Hx2) -Hx2 //
]
qed-.

lemma sdj_inv_nn: ∀g1,g2. g1 ∥ g2 → ∀f1,f2. ↑f1 = g1 → ↑f2 = g2 → ⊥.
#g1 #g2 * -g1 -g2
#f1 #f2 #g1 #g2 #H #H1 #H2 #x1 #x2 #Hx1 #Hx2 destruct
[ elim (discr_next_push … Hx1)
| elim (discr_next_push … Hx2)
| elim (discr_next_push … Hx1)
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma sdj_inv_nx: ∀g1,g2. g1 ∥ g2 → ∀f1. ↑f1 = g1 →
                  ∃∃f2. f1 ∥ f2 & ⫯f2 = g2.
#g1 #g2 elim (pn_split g2) * #f2 #H2 #H #f1 #H1
[ lapply (sdj_inv_np … H … H1 H2) -H /2 width=3 by ex2_intro/
| elim (sdj_inv_nn … H … H1 H2)
]
qed-.

lemma sdj_inv_xn: ∀g1,g2. g1 ∥ g2 → ∀f2. ↑f2 = g2 →
                  ∃∃f1. f1 ∥ f2 & ⫯f1 = g1.
#g1 #g2 elim (pn_split g1) * #f1 #H1 #H #f2 #H2
[ lapply (sdj_inv_pn … H … H1 H2) -H /2 width=3 by ex2_intro/
| elim (sdj_inv_nn … H … H1 H2)
]
qed-.

lemma sdj_inv_xp: ∀g1,g2. g1 ∥ g2 → ∀f2. ⫯f2 = g2 →
                  ∨∨ ∃∃f1. f1 ∥ f2 & ⫯f1 = g1
                   | ∃∃f1. f1 ∥ f2 & ↑f1 = g1.
#g1 #g2 elim (pn_split g1) * #f1 #H1 #H #f2 #H2
[ lapply (sdj_inv_pp … H … H1 H2) | lapply (sdj_inv_np … H … H1 H2) ] -H -H2
/3 width=3 by ex2_intro, or_introl, or_intror/
qed-.

lemma sdj_inv_px: ∀g1,g2. g1 ∥ g2 → ∀f1. ⫯f1 = g1 →
                  ∨∨ ∃∃f2. f1 ∥ f2 & ⫯f2 = g2
                   | ∃∃f2. f1 ∥ f2 & ↑f2 = g2.
#g1 #g2 elim (pn_split g2) * #f2 #H2 #H #f1 #H1
[ lapply (sdj_inv_pp … H … H1 H2) | lapply (sdj_inv_pn … H … H1 H2) ] -H -H1
/3 width=3 by ex2_intro, or_introl, or_intror/
qed-.

(* Properties with isid *****************************************************)

corec lemma sdj_isid_dx: ∀f2. 𝐈❪f2❫ → ∀f1. f1 ∥ f2.
#f2 * -f2
#f2 #g2 #Hf2 #H2 #f1 cases (pn_split f1) *
/3 width=5 by sdj_np, sdj_pp/
qed.

corec lemma sdj_isid_sn: ∀f1. 𝐈❪f1❫ → ∀f2. f1 ∥ f2.
#f1 * -f1
#f1 #g1 #Hf1 #H1 #f2 cases (pn_split f2) *
/3 width=5 by sdj_pn, sdj_pp/
qed.

(* Inversion lemmas with isid ***********************************************)

corec lemma sdj_inv_refl: ∀f. f ∥ f →  𝐈❪f❫.
#f cases (pn_split f) * #g #Hg #H
[ lapply (sdj_inv_pp … H … Hg Hg) -H /3 width=3 by isid_push/
| elim (sdj_inv_nn … H … Hg Hg)
]
qed-.
