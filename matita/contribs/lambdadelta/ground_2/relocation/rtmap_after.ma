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

include "ground_2/notation/relations/rafter_3.ma".
include "ground_2/relocation/rtmap_istot.ma".

(* RELOCATION MAP ***********************************************************)

coinductive after: relation3 rtmap rtmap rtmap ≝
| after_refl: ∀f1,f2,f,g1,g2,g.
              after f1 f2 f → ↑f1 = g1 → ↑f2 = g2 → ↑f = g → after g1 g2 g
| after_push: ∀f1,f2,f,g1,g2,g.
              after f1 f2 f → ↑f1 = g1 → ⫯f2 = g2 → ⫯f = g → after g1 g2 g
| after_next: ∀f1,f2,f,g1,g.
              after f1 f2 f → ⫯f1 = g1 → ⫯f = g → after g1 f2 g
.

interpretation "relational composition (rtmap)"
   'RAfter f1 f2 f = (after f1 f2 f).

definition H_after_inj: predicate rtmap ≝
                        λf1. 𝐓⦃f1⦄ →
                        ∀f,f21,f22. f1 ⊚ f21 ≡ f → f1 ⊚ f22 ≡ f → f21 ≗ f22.

(* Basic inversion lemmas ***************************************************)

lemma after_inv_ppx: ∀g1,g2,g. g1 ⊚ g2 ≡ g → ∀f1,f2. ↑f1 = g1 → ↑f2 = g2 →
                     ∃∃f. f1 ⊚ f2 ≡ f & ↑f = g.
#g1 #g2 #g * -g1 -g2 -g #f1 #f2 #f #g1
[ #g2 #g #Hf #H1 #H2 #H #x1 #x2 #Hx1 #Hx2 destruct
  >(injective_push … Hx1) >(injective_push … Hx2) -x2 -x1
  /2 width=3 by ex2_intro/
| #g2 #g #_ #_ #H2 #_ #x1 #x2 #_ #Hx2 destruct
  elim (discr_push_next … Hx2)
| #g #_ #H1 #_ #x1 #x2 #Hx1 #_ destruct
  elim (discr_push_next … Hx1)
]
qed-.

lemma after_inv_pnx: ∀g1,g2,g. g1 ⊚ g2 ≡ g → ∀f1,f2. ↑f1 = g1 → ⫯f2 = g2 →
                     ∃∃f. f1 ⊚ f2 ≡ f & ⫯f = g.
#g1 #g2 #g * -g1 -g2 -g #f1 #f2 #f #g1
[ #g2 #g #_ #_ #H2 #_ #x1 #x2 #_ #Hx2 destruct
  elim (discr_next_push … Hx2)
| #g2 #g #Hf #H1 #H2 #H3 #x1 #x2 #Hx1 #Hx2 destruct
  >(injective_push … Hx1) >(injective_next … Hx2) -x2 -x1
  /2 width=3 by ex2_intro/
| #g #_ #H1 #_ #x1 #x2 #Hx1 #_ destruct
  elim (discr_push_next … Hx1)
]
qed-.

lemma after_inv_nxx: ∀g1,f2,g. g1 ⊚ f2 ≡ g → ∀f1. ⫯f1 = g1 →
                     ∃∃f. f1 ⊚ f2 ≡ f & ⫯f = g.
#g1 #f2 #g * -g1 -f2 -g #f1 #f2 #f #g1
[ #g2 #g #_ #H1 #_ #_ #x1 #Hx1 destruct
  elim (discr_next_push … Hx1)
| #g2 #g #_ #H1 #_ #_ #x1 #Hx1 destruct
  elim (discr_next_push … Hx1)
| #g #Hf #H1 #H #x1 #Hx1 destruct
  >(injective_next … Hx1) -x1
  /2 width=3 by ex2_intro/
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma after_inv_ppp: ∀g1,g2,g. g1 ⊚ g2 ≡ g →
                     ∀f1,f2,f. ↑f1 = g1 → ↑f2 = g2 → ↑f = g → f1 ⊚ f2 ≡ f.
#g1 #g2 #g #Hg #f1 #f2 #f #H1 #H2 #H elim (after_inv_ppx … Hg … H1 H2) -g1 -g2
#x #Hf #Hx destruct <(injective_push … Hx) -f //
qed-.

lemma after_inv_ppn: ∀g1,g2,g. g1 ⊚ g2 ≡ g →
                     ∀f1,f2,f. ↑f1 = g1 → ↑f2 = g2 → ⫯f = g → ⊥.
#g1 #g2 #g #Hg #f1 #f2 #f #H1 #H2 #H elim (after_inv_ppx … Hg … H1 H2) -g1 -g2
#x #Hf #Hx destruct elim (discr_push_next … Hx)
qed-.

lemma after_inv_pnn: ∀g1,g2,g. g1 ⊚ g2 ≡ g →
                    ∀f1,f2,f. ↑f1 = g1 → ⫯f2 = g2 → ⫯f = g → f1 ⊚ f2 ≡ f.
#g1 #g2 #g #Hg #f1 #f2 #f #H1 #H2 #H elim (after_inv_pnx … Hg … H1 H2) -g1 -g2
#x #Hf #Hx destruct <(injective_next … Hx) -f //
qed-.

lemma after_inv_pnp: ∀g1,g2,g. g1 ⊚ g2 ≡ g →
                     ∀f1,f2,f. ↑f1 = g1 → ⫯f2 = g2 → ↑f = g → ⊥.
#g1 #g2 #g #Hg #f1 #f2 #f #H1 #H2 #H elim (after_inv_pnx … Hg … H1 H2) -g1 -g2
#x #Hf #Hx destruct elim (discr_next_push … Hx)
qed-.

lemma after_inv_nxn: ∀g1,f2,g. g1 ⊚ f2 ≡ g →
                     ∀f1,f. ⫯f1 = g1 → ⫯f = g → f1 ⊚ f2 ≡ f.
#g1 #f2 #g #Hg #f1 #f #H1 #H elim (after_inv_nxx … Hg … H1) -g1
#x #Hf #Hx destruct <(injective_next … Hx) -f //
qed-.

lemma after_inv_nxp: ∀g1,f2,g. g1 ⊚ f2 ≡ g →
                     ∀f1,f. ⫯f1 = g1 → ↑f = g → ⊥.
#g1 #f2 #g #Hg #f1 #f #H1 #H elim (after_inv_nxx … Hg … H1) -g1
#x #Hf #Hx destruct elim (discr_next_push … Hx)
qed-.

lemma after_inv_pxp: ∀g1,g2,g. g1 ⊚ g2 ≡ g →
                     ∀f1,f. ↑f1 = g1 → ↑f = g →
                     ∃∃f2. f1 ⊚ f2 ≡ f & ↑f2 = g2.
#g1 * * [2: #m2] #g2 #g #Hg #f1 #f #H1 #H
[ elim (after_inv_pnp … Hg … H1 … H) -g1 -g -f1 -f //
| lapply (after_inv_ppp … Hg … H1 … H) -g1 -g /2 width=3 by ex2_intro/
]
qed-.

lemma after_inv_pxn: ∀g1,g2,g. g1 ⊚ g2 ≡ g →
                     ∀f1,f. ↑f1 = g1 → ⫯f = g →
                     ∃∃f2. f1 ⊚ f2 ≡ f & ⫯f2 = g2.
#g1 * * [2: #m2] #g2 #g #Hg #f1 #f #H1 #H
[ lapply (after_inv_pnn … Hg … H1 … H) -g1 -g /2 width=3 by ex2_intro/
| elim (after_inv_ppn … Hg … H1 … H) -g1 -g -f1 -f //
]
qed-.

lemma after_inv_xxp: ∀g1,g2,g. g1 ⊚ g2 ≡ g → ∀f. ↑f = g →
                     ∃∃f1,f2. f1 ⊚ f2 ≡ f & ↑f1 = g1 & ↑f2 = g2.
* * [2: #m1 ] #g1 #g2 #g #Hg #f #H
[ elim (after_inv_nxp … Hg … H) -g2 -g -f //
| elim (after_inv_pxp … Hg … H) -g /2 width=5 by ex3_2_intro/
]
qed-.

lemma after_inv_xxn: ∀g1,g2,g. g1 ⊚ g2 ≡ g → ∀f. ⫯f = g →
                     (∃∃f1,f2. f1 ⊚ f2 ≡ f & ↑f1 = g1 & ⫯f2 = g2) ∨
                     ∃∃f1. f1 ⊚ g2 ≡ f & ⫯f1 = g1.
* * [2: #m1 ] #g1 #g2 #g #Hg #f #H
[ /4 width=5 by after_inv_nxn, or_intror, ex2_intro/
| elim (after_inv_pxn … Hg … H) -g
  /3 width=5 by or_introl, ex3_2_intro/
]
qed-.

lemma after_inv_pxx: ∀g1,g2,g. g1 ⊚ g2 ≡ g → ∀f1. ↑f1 = g1 →
                     (∃∃f2,f. f1 ⊚ f2 ≡ f & ↑f2 = g2 & ↑f = g) ∨
                     (∃∃f2,f. f1 ⊚ f2 ≡ f & ⫯f2 = g2 & ⫯f = g).
#g1 * * [2: #m2 ] #g2 #g #Hg #f1 #H
[  elim (after_inv_pnx … Hg … H) -g1
  /3 width=5 by or_intror, ex3_2_intro/
| elim (after_inv_ppx … Hg … H) -g1
  /3 width=5 by or_introl, ex3_2_intro/
]
qed-.

(* Basic properties *********************************************************)

corec lemma after_eq_repl_back_2: ∀f1,f. eq_repl_back (λf2. f2 ⊚ f1 ≡ f).
#f1 #f #f2 * -f2 -f1 -f
#f21 #f1 #f #g21 [1,2: #g1 ] #g #Hf #H21 [1,2: #H1 ] #H #g22 #H0
[ cases (eq_inv_px …  H0 …  H21) -g21 /3 width=7 by after_refl/
| cases (eq_inv_px …  H0 …  H21) -g21 /3 width=7 by after_push/
| cases (eq_inv_nx …  H0 …  H21) -g21 /3 width=5 by after_next/ 
]
qed-.

lemma after_eq_repl_fwd_2: ∀f1,f. eq_repl_fwd (λf2. f2 ⊚ f1 ≡ f).
#f1 #f @eq_repl_sym /2 width=3 by after_eq_repl_back_2/
qed-.

corec lemma after_eq_repl_back_1: ∀f2,f. eq_repl_back (λf1. f2 ⊚ f1 ≡ f).
#f2 #f #f1 * -f2 -f1 -f
#f2 #f11 #f #g2 [1,2: #g11 ] #g #Hf #H2 [1,2: #H11 ] #H #g2 #H0
[ cases (eq_inv_px …  H0 …  H11) -g11 /3 width=7 by after_refl/
| cases (eq_inv_nx …  H0 …  H11) -g11 /3 width=7 by after_push/
| @(after_next … H2 H) /2 width=5 by/
]
qed-.

lemma after_eq_repl_fwd_1: ∀f2,f. eq_repl_fwd (λf1. f2 ⊚ f1 ≡ f).
#f2 #f @eq_repl_sym /2 width=3 by after_eq_repl_back_1/
qed-.

corec lemma after_eq_repl_back_0: ∀f1,f2. eq_repl_back (λf. f2 ⊚ f1 ≡ f).
#f2 #f1 #f * -f2 -f1 -f
#f2 #f1 #f01 #g2 [1,2: #g1 ] #g01 #Hf01 #H2 [1,2: #H1 ] #H01 #g02 #H0
[ cases (eq_inv_px …  H0 …  H01) -g01 /3 width=7 by after_refl/
| cases (eq_inv_nx …  H0 …  H01) -g01 /3 width=7 by after_push/
| cases (eq_inv_nx …  H0 …  H01) -g01 /3 width=5 by after_next/ 
]
qed-.

lemma after_eq_repl_fwd_0: ∀f2,f1. eq_repl_fwd (λf. f2 ⊚ f1 ≡ f).
#f2 #f1 @eq_repl_sym /2 width=3 by after_eq_repl_back_0/
qed-.

(* Main properties **********************************************************)

corec theorem after_trans1: ∀f0,f3,f4. f0 ⊚ f3 ≡ f4 →
                            ∀f1,f2. f1 ⊚ f2 ≡ f0 →
                            ∀f. f2 ⊚ f3 ≡ f → f1 ⊚ f ≡ f4.
#f0 #f3 #f4 * -f0 -f3 -f4 #f0 #f3 #f4 #g0 [1,2: #g3 ] #g4
[ #Hf4 #H0 #H3 #H4 #g1 #g2 #Hg0 #g #Hg
  cases (after_inv_xxp … Hg0 … H0) -g0
  #f1 #f2 #Hf0 #H1 #H2
  cases (after_inv_ppx … Hg … H2 H3) -g2 -g3
  #f #Hf #H /3 width=7 by after_refl/
| #Hf4 #H0 #H3 #H4 #g1 #g2 #Hg0 #g #Hg
  cases (after_inv_xxp … Hg0 … H0) -g0
  #f1 #f2 #Hf0 #H1 #H2
  cases (after_inv_pnx … Hg … H2 H3) -g2 -g3
  #f #Hf #H /3 width=7 by after_push/
| #Hf4 #H0 #H4 #g1 #g2 #Hg0 #g #Hg
  cases (after_inv_xxn … Hg0 … H0) -g0 *
  [ #f1 #f2 #Hf0 #H1 #H2
    cases (after_inv_nxx … Hg … H2) -g2
    #f #Hf #H /3 width=7 by after_push/
  | #f1 #Hf0 #H1 /3 width=6 by after_next/
  ]
]
qed-.

corec theorem after_trans2: ∀f1,f0,f4. f1 ⊚ f0 ≡ f4 →
                            ∀f2, f3. f2 ⊚ f3 ≡ f0 →
                            ∀f. f1 ⊚ f2 ≡ f → f ⊚ f3 ≡ f4.
#f1 #f0 #f4 * -f1 -f0 -f4 #f1 #f0 #f4 #g1 [1,2: #g0 ] #g4
[ #Hf4 #H1 #H0 #H4 #g2 #g3 #Hg0 #g #Hg
  cases (after_inv_xxp … Hg0 … H0) -g0
  #f2 #f3 #Hf0 #H2 #H3
  cases (after_inv_ppx … Hg … H1 H2) -g1 -g2
  #f #Hf #H /3 width=7 by after_refl/
| #Hf4 #H1 #H0 #H4 #g2 #g3 #Hg0 #g #Hg
  cases (after_inv_xxn … Hg0 … H0) -g0 *
  [ #f2 #f3 #Hf0 #H2 #H3
    cases (after_inv_ppx … Hg … H1 H2) -g1 -g2
    #f #Hf #H /3 width=7 by after_push/
  | #f2 #Hf0 #H2
    cases (after_inv_pnx … Hg … H1 H2) -g1 -g2
    #f #Hf #H /3 width=6 by after_next/
  ]
| #Hf4 #H1 #H4 #f2 #f3 #Hf0 #g #Hg
  cases (after_inv_nxx … Hg … H1) -g1
  #f #Hg #H /3 width=6 by after_next/
]
qed-.

(* Main inversion lemmas on after *******************************************)

corec theorem after_mono: ∀f1,f2,x,y. f1 ⊚ f2 ≡ x → f1 ⊚ f2 ≡ y → x ≗ y.
#f1 #f2 #x #y * -f1 -f2 -x
#f1 #f2 #x #g1 [1,2: #g2 ] #g #Hx #H1 [1,2: #H2 ] #H0x #Hy
[ cases (after_inv_ppx … Hy … H1 H2) -g1 -g2 /3 width=8 by eq_push/
| cases (after_inv_pnx … Hy … H1 H2) -g1 -g2 /3 width=8 by eq_next/
| cases (after_inv_nxx … Hy … H1) -g1 /3 width=8 by eq_next/
]
qed-.

lemma after_mono_eq: ∀f1,f2,f. f1 ⊚ f2 ≡ f → ∀g1,g2,g. g1 ⊚ g2 ≡ g →
                     f1 ≗ g1 → f2 ≗ g2 → f ≗ g.
/4 width=4 by after_mono, after_eq_repl_back_1, after_eq_repl_back_2/ qed-.

(* Properties on tls ********************************************************)

lemma after_tls: ∀n,f1,f2,f. @⦃0, f1⦄ ≡ n → 
                 f1 ⊚ f2 ≡ f → ⫱*[n]f1 ⊚ f2 ≡ ⫱*[n]f.
#n elim n -n //
#n #IH #f1 #f2 #f #Hf1 #Hf cases (at_inv_pxn … Hf1) -Hf1 [ |*: // ]
#g1 #Hg1 #H1 cases (after_inv_nxx … Hf … H1) -Hf /2 width=1 by/
qed.

(* Inversion lemmas on isid *************************************************)

corec lemma isid_after_sn: ∀f1. 𝐈⦃f1⦄ → ∀f2. f1 ⊚ f2 ≡ f2.
#f1 * -f1 #f1 #g1 #Hf1 #H1 #f2 cases (pn_split f2) * #g2 #H2
/3 width=7 by after_push, after_refl/
qed-.

corec lemma isid_after_dx: ∀f2. 𝐈⦃f2⦄ → ∀f1. f1 ⊚ f2 ≡ f1.
#f2 * -f2 #f2 #g2 #Hf2 #H2 #f1 cases (pn_split f1) * #g1 #H1
[ /3 width=7 by after_refl/
| @(after_next … H1 H1) /3 width=3 by isid_push/
]
qed-.

lemma after_isid_inv_sn: ∀f1,f2,f. f1 ⊚ f2 ≡ f →  𝐈⦃f1⦄ → f2 ≗ f.
/3 width=6 by isid_after_sn, after_mono/
qed-.

lemma after_isid_inv_dx: ∀f1,f2,f. f1 ⊚ f2 ≡ f →  𝐈⦃f2⦄ → f1 ≗ f.
/3 width=6 by isid_after_dx, after_mono/
qed-.

corec lemma after_fwd_isid1: ∀f1,f2,f. f1 ⊚ f2 ≡ f → 𝐈⦃f⦄ → 𝐈⦃f1⦄.
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 [1,2: #g2 ] #g #Hf #H1 [1,2: #H2 ] #H0 #H
[ /4 width=6 by isid_inv_push, isid_push/ ]
cases (isid_inv_next … H … H0)
qed-.

corec lemma after_fwd_isid2: ∀f1,f2,f. f1 ⊚ f2 ≡ f → 𝐈⦃f⦄ → 𝐈⦃f2⦄.
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 [1,2: #g2 ] #g #Hf #H1 [1,2: #H2 ] #H0 #H
[ /4 width=6 by isid_inv_push, isid_push/ ]
cases (isid_inv_next … H … H0)
qed-.

lemma after_inv_isid3: ∀f1,f2,f. f1 ⊚ f2 ≡ f → 𝐈⦃f⦄ → 𝐈⦃f1⦄ ∧ 𝐈⦃f2⦄.
/3 width=4 by after_fwd_isid2, after_fwd_isid1, conj/ qed-.

(* Forward lemmas on at *****************************************************)

lemma after_at_fwd: ∀i,i1,f. @⦃i1, f⦄ ≡ i → ∀f2,f1. f2 ⊚ f1 ≡ f →
                    ∃∃i2. @⦃i1, f1⦄ ≡ i2 & @⦃i2, f2⦄ ≡ i.
#i elim i -i [2: #i #IH ] #i1 #f #Hf #f2 #f1 #Hf21
[ elim (at_inv_xxn … Hf) -Hf [1,3:* |*: // ]
  [1: #g #j1 #Hg #H0 #H |2,4: #g #Hg #H ]
| elim (at_inv_xxp … Hf) -Hf //
  #g #H1 #H
]
[2: elim (after_inv_xxn … Hf21 … H) -f *
    [ #g2 #g1 #Hg21 #H2 #H1 | #g2 #Hg21 #H2 ]
|*: elim (after_inv_xxp … Hf21 … H) -f
    #g2 #g1 #Hg21 #H2 #H1
]
[4: -Hg21 |*: elim (IH … Hg … Hg21) -g -IH ]
/3 width=9 by at_refl, at_push, at_next, ex2_intro/
qed-.

lemma after_fwd_at: ∀i,i2,i1,f1,f2. @⦃i1, f1⦄ ≡ i2 → @⦃i2, f2⦄ ≡ i →
                    ∀f. f2 ⊚ f1 ≡ f → @⦃i1, f⦄ ≡ i.
#i elim i -i [2: #i #IH ] #i2 #i1 #f1 #f2 #Hf1 #Hf2 #f #Hf
[ elim (at_inv_xxn … Hf2) -Hf2 [1,3: * |*: // ]
  #g2 [ #j2 ] #Hg2 [ #H22 ] #H20
  [ elim (at_inv_xxn … Hf1 … H22) -i2 *
    #g1 [ #j1 ] #Hg1 [ #H11 ] #H10
    [ elim (after_inv_ppx … Hf … H20 H10) -f1 -f2 /3 width=7 by at_push/
    | elim (after_inv_pnx … Hf … H20 H10) -f1 -f2 /3 width=6 by at_next/
    ]
  | elim (after_inv_nxx … Hf … H20) -f2 /3 width=7 by at_next/
  ]
| elim (at_inv_xxp … Hf2) -Hf2 // #g2 #H22 #H20
  elim (at_inv_xxp … Hf1 … H22) -i2 #g1 #H11 #H10
  elim (after_inv_ppx … Hf … H20 H10) -f1 -f2 /2 width=2 by at_refl/
]
qed-.

lemma after_fwd_at2: ∀f,i1,i. @⦃i1, f⦄ ≡ i → ∀f1,i2. @⦃i1, f1⦄ ≡ i2 →
                     ∀f2. f2 ⊚ f1 ≡ f → @⦃i2, f2⦄ ≡ i.
#f #i1 #i #Hf #f1 #i2 #Hf1 #f2 #H elim (after_at_fwd … Hf … H) -f
#j1 #H #Hf2 <(at_mono … Hf1 … H) -i1 -i2 //
qed-.

lemma after_fwd_at1: ∀i,i2,i1,f,f2. @⦃i1, f⦄ ≡ i → @⦃i2, f2⦄ ≡ i →
                     ∀f1. f2 ⊚ f1 ≡ f → @⦃i1, f1⦄ ≡ i2.
#i elim i -i [2: #i #IH ] #i2 #i1 #f #f2 #Hf #Hf2 #f1 #Hf1
[ elim (at_inv_xxn … Hf) -Hf [1,3: * |*: // ]
  #g [ #j1 ] #Hg [ #H01 ] #H00
  elim (at_inv_xxn … Hf2) -Hf2 [1,3,5,7: * |*: // ]
  #g2 [1,3: #j2 ] #Hg2 [1,2: #H22 ] #H20
  [ elim (after_inv_pxp … Hf1 … H20 H00) -f2 -f /3 width=7 by at_push/
  | elim (after_inv_pxn … Hf1 … H20 H00) -f2 -f /3 width=5 by at_next/
  | elim (after_inv_nxp … Hf1 … H20 H00)
  | /4 width=9 by after_inv_nxn, at_next/
  ]
| elim (at_inv_xxp … Hf) -Hf // #g #H01 #H00
  elim (at_inv_xxp … Hf2) -Hf2 // #g2 #H21 #H20
  elim (after_inv_pxp … Hf1 … H20 H00) -f2 -f /3 width=2 by at_refl/
]
qed-.

(* Forward lemmas on istot **************************************************)

lemma after_istot_fwd: ∀f2,f1,f. f2 ⊚ f1 ≡ f → 𝐓⦃f2⦄ → 𝐓⦃f1⦄ → 𝐓⦃f⦄.
#f2 #f1 #f #Hf #Hf2 #Hf1 #i1 elim (Hf1 i1) -Hf1
#i2 #Hf1 elim (Hf2 i2) -Hf2
/3 width=7 by after_fwd_at, ex_intro/
qed-.

lemma after_fwd_istot_dx: ∀f2,f1,f. f2 ⊚ f1 ≡ f → 𝐓⦃f⦄ → 𝐓⦃f1⦄.
#f2 #f1 #f #H #Hf #i1 elim (Hf i1) -Hf
#i2 #Hf elim (after_at_fwd … Hf … H) -f /2 width=2 by ex_intro/
qed-.

lemma after_fwd_istot_sn: ∀f2,f1,f. f2 ⊚ f1 ≡ f → 𝐓⦃f⦄ → 𝐓⦃f2⦄.
#f2 #f1 #f #H #Hf #i1 elim (Hf i1) -Hf
#i #Hf elim (after_at_fwd … Hf … H) -f
#i2 #Hf1 #Hf2 lapply (at_increasing … Hf1) -f1
#Hi12 elim (at_le_ex … Hf2 … Hi12) -i2 /2 width=2 by ex_intro/
qed-.

lemma after_inv_istot: ∀f2,f1,f. f2 ⊚ f1 ≡ f → 𝐓⦃f⦄ → 𝐓⦃f2⦄ ∧ 𝐓⦃f1⦄.
/3 width=4 by after_fwd_istot_sn, after_fwd_istot_dx, conj/ qed-.

lemma after_at1_fwd: ∀f1,i1,i2. @⦃i1, f1⦄ ≡ i2 → ∀f2. 𝐓⦃f2⦄ → ∀f. f2 ⊚ f1 ≡ f →
                     ∃∃i. @⦃i2, f2⦄ ≡ i & @⦃i1, f⦄ ≡ i.
#f1 #i1 #i2 #Hf1 #f2 #Hf2 #f #Hf elim (Hf2 i2) -Hf2
/3 width=8 by after_fwd_at, ex2_intro/
qed-.

lemma after_fwd_isid_sn: ∀f2,f1,f. 𝐓⦃f⦄ → f2 ⊚ f1 ≡ f → f1 ≗ f → 𝐈⦃f2⦄.
#f2 #f1 #f #H #Hf elim (after_inv_istot … Hf H) -H
#Hf2 #Hf1 #H @isid_at_total // -Hf2
#i2 #i #Hf2 elim (Hf1 i2) -Hf1
#i0 #Hf1 lapply (at_increasing … Hf1)
#Hi20 lapply (after_fwd_at2 … i0 … Hf1 … Hf) -Hf
/3 width=7 by at_eq_repl_back, at_mono, at_id_le/
qed-.

lemma after_fwd_isid_dx: ∀f2,f1,f.  𝐓⦃f⦄ → f2 ⊚ f1 ≡ f → f2 ≗ f → 𝐈⦃f1⦄.
#f2 #f1 #f #H #Hf elim (after_inv_istot … Hf H) -H
#Hf2 #Hf1 #H2 @isid_at_total // -Hf1
#i1 #i2 #Hi12 elim (after_at1_fwd … Hi12 … Hf) -f1
/3 width=8 by at_inj, at_eq_repl_back/
qed-.

corec fact after_inj_O_aux: ∀f1. @⦃0, f1⦄ ≡ 0 → H_after_inj f1.
#f1 #H1f1 #H2f1 #f #f21 #f22 #H1f #H2f
cases (at_inv_pxp … H1f1) -H1f1 [ |*: // ] #g1 #H1
lapply (istot_inv_push … H2f1 … H1) -H2f1 #H2g1
cases (H2g1 0) #n #Hn
cases (after_inv_pxx … H1f … H1) -H1f * #g21 #g #H1g #H21 #H
[ cases (after_inv_pxp … H2f … H1 H) -f1 -f #g22 #H2g #H22
  @(eq_push … H21 H22) -f21 -f22
| cases (after_inv_pxn … H2f … H1 H) -f1 -f #g22 #H2g #H22
  @(eq_next … H21 H22) -f21 -f22
]
@(after_inj_O_aux (⫱*[n]g1) … (⫱*[n]g)) -after_inj_O_aux
/2 width=1 by after_tls, istot_tls, at_pxx_tls/
qed-.

fact after_inj_aux: (∀f1. @⦃0, f1⦄ ≡ 0 → H_after_inj f1) →
                    ∀i2,f1. @⦃0, f1⦄ ≡ i2 → H_after_inj f1.
#H0 #i2 elim i2 -i2 /2 width=1 by/ -H0
#i2 #IH #f1 #H1f1 #H2f1 #f #f21 #f22 #H1f #H2f
elim (at_inv_pxn … H1f1) -H1f1 [ |*: // ] #g1 #H1g1 #H1
elim (after_inv_nxx … H1f … H1) -H1f #g #H1g #H
lapply (after_inv_nxn … H2f … H1 H) -f #H2g
/3 width=6 by istot_inv_next/
qed-.

theorem after_inj: ∀f1. H_after_inj f1.
#f1 #H cases (H 0) /3 width=7 by after_inj_aux, after_inj_O_aux/
qed-.
