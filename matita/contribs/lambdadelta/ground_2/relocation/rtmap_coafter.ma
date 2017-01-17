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

include "ground_2/notation/relations/rcoafter_3.ma".
include "ground_2/relocation/rtmap_sor.ma".
include "ground_2/relocation/rtmap_after.ma".

(* RELOCATION MAP ***********************************************************)

coinductive coafter: relation3 rtmap rtmap rtmap ≝
| coafter_refl: ∀f1,f2,f,g1,g2,g. coafter f1 f2 f →
                ↑f1 = g1 → ↑f2 = g2 → ↑f = g → coafter g1 g2 g
| coafter_push: ∀f1,f2,f,g1,g2,g. coafter f1 f2 f →
                ↑f1 = g1 → ⫯f2 = g2 → ⫯f = g → coafter g1 g2 g
| coafter_next: ∀f1,f2,f,g1,g. coafter f1 f2 f →
                ⫯f1 = g1 → ↑f = g → coafter g1 f2 g
.

interpretation "relational co-composition (rtmap)"
   'RCoAfter f1 f2 f = (coafter f1 f2 f).

definition H_coafter_inj: predicate rtmap ≝
                          λf1. 𝐓⦃f1⦄ →
                          ∀f,f21,f22. f1 ~⊚ f21 ≡ f → f1 ~⊚ f22 ≡ f → f21 ≗ f22.

definition H_coafter_fwd_isid2: predicate rtmap ≝
                                λf1. ∀f2,f. f1 ~⊚ f2 ≡ f → 𝐓⦃f1⦄ → 𝐈⦃f⦄ → 𝐈⦃f2⦄.

definition H_coafter_isfin2_fwd: predicate rtmap ≝
                                 λf1. ∀f2. 𝐅⦃f2⦄ → 𝐓⦃f1⦄ → ∀f. f1 ~⊚ f2 ≡ f →  𝐅⦃f⦄.

(* Basic inversion lemmas ***************************************************)

lemma coafter_inv_ppx: ∀g1,g2,g. g1 ~⊚ g2 ≡ g → ∀f1,f2. ↑f1 = g1 → ↑f2 = g2 →
                       ∃∃f. f1 ~⊚ f2 ≡ f & ↑f = g.
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

lemma coafter_inv_pnx: ∀g1,g2,g. g1 ~⊚ g2 ≡ g → ∀f1,f2. ↑f1 = g1 → ⫯f2 = g2 →
                       ∃∃f. f1 ~⊚ f2 ≡ f & ⫯f = g.
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

lemma coafter_inv_nxx: ∀g1,f2,g. g1 ~⊚ f2 ≡ g → ∀f1. ⫯f1 = g1 →
                       ∃∃f. f1 ~⊚ f2 ≡ f & ↑f = g.
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

lemma coafter_inv_ppp: ∀g1,g2,g. g1 ~⊚ g2 ≡ g →
                       ∀f1,f2,f. ↑f1 = g1 → ↑f2 = g2 → ↑f = g → f1 ~⊚ f2 ≡ f.
#g1 #g2 #g #Hg #f1 #f2 #f #H1 #H2 #H
elim (coafter_inv_ppx … Hg … H1 H2) -g1 -g2 #x #Hf #Hx destruct
<(injective_push … Hx) -f //
qed-.

lemma coafter_inv_ppn: ∀g1,g2,g. g1 ~⊚ g2 ≡ g →
                       ∀f1,f2,f. ↑f1 = g1 → ↑f2 = g2 → ⫯f = g → ⊥.
#g1 #g2 #g #Hg #f1 #f2 #f #H1 #H2 #H
elim (coafter_inv_ppx … Hg … H1 H2) -g1 -g2 #x #Hf #Hx destruct
elim (discr_push_next … Hx)
qed-.

lemma coafter_inv_pnn: ∀g1,g2,g. g1 ~⊚ g2 ≡ g →
                       ∀f1,f2,f. ↑f1 = g1 → ⫯f2 = g2 → ⫯f = g → f1 ~⊚ f2 ≡ f.
#g1 #g2 #g #Hg #f1 #f2 #f #H1 #H2 #H
elim (coafter_inv_pnx … Hg … H1 H2) -g1 -g2 #x #Hf #Hx destruct
<(injective_next … Hx) -f //
qed-.

lemma coafter_inv_pnp: ∀g1,g2,g. g1 ~⊚ g2 ≡ g →
                       ∀f1,f2,f. ↑f1 = g1 → ⫯f2 = g2 → ↑f = g → ⊥.
#g1 #g2 #g #Hg #f1 #f2 #f #H1 #H2 #H
elim (coafter_inv_pnx … Hg … H1 H2) -g1 -g2 #x #Hf #Hx destruct
elim (discr_next_push … Hx)
qed-.

lemma coafter_inv_nxp: ∀g1,f2,g. g1 ~⊚ f2 ≡ g →
                       ∀f1,f. ⫯f1 = g1 → ↑f = g → f1 ~⊚ f2 ≡ f.
#g1 #f2 #g #Hg #f1 #f #H1 #H
elim (coafter_inv_nxx … Hg … H1) -g1 #x #Hf #Hx destruct
<(injective_push … Hx) -f //
qed-.

lemma coafter_inv_nxn: ∀g1,f2,g. g1 ~⊚ f2 ≡ g →
                       ∀f1,f. ⫯f1 = g1 → ⫯f = g → ⊥.
#g1 #f2 #g #Hg #f1 #f #H1 #H
elim (coafter_inv_nxx … Hg … H1) -g1 #x #Hf #Hx destruct
elim (discr_push_next … Hx)
qed-.

lemma coafter_inv_pxp: ∀g1,g2,g. g1 ~⊚ g2 ≡ g →
                       ∀f1,f. ↑f1 = g1 → ↑f = g →
                       ∃∃f2. f1 ~⊚ f2 ≡ f & ↑f2 = g2.
#g1 #g2 #g #Hg #f1 #f #H1 #H elim (pn_split g2) * #f2 #H2
[ lapply (coafter_inv_ppp … Hg … H1 H2 H) -g1 -g /2 width=3 by ex2_intro/
| elim (coafter_inv_pnp … Hg … H1 H2 H)
]
qed-.

lemma coafter_inv_pxn: ∀g1,g2,g. g1 ~⊚ g2 ≡ g →
                       ∀f1,f. ↑f1 = g1 → ⫯f = g →
                       ∃∃f2. f1 ~⊚ f2 ≡ f & ⫯f2 = g2.
#g1 #g2 #g #Hg #f1 #f #H1 #H elim (pn_split g2) * #f2 #H2
[ elim (coafter_inv_ppn … Hg … H1 H2 H)
| lapply (coafter_inv_pnn … Hg … H1 … H) -g1 -g /2 width=3 by ex2_intro/
]
qed-.

lemma coafter_inv_xxn: ∀g1,g2,g. g1 ~⊚ g2 ≡ g → ∀f. ⫯f = g →
                       ∃∃f1,f2. f1 ~⊚ f2 ≡ f & ↑f1 = g1 & ⫯f2 = g2.
#g1 #g2 #g #Hg #f #H elim (pn_split g1) * #f1 #H1
[ elim (coafter_inv_pxn … Hg … H1 H) -g /2 width=5 by ex3_2_intro/
| elim (coafter_inv_nxn … Hg … H1 H)
]
qed-.

lemma coafter_inv_xxp: ∀g1,g2,g. g1 ~⊚ g2 ≡ g → ∀f. ↑f = g →
                       (∃∃f1,f2. f1 ~⊚ f2 ≡ f & ↑f1 = g1 & ↑f2 = g2) ∨
                       ∃∃f1. f1 ~⊚ g2 ≡ f & ⫯f1 = g1.
#g1 #g2 #g #Hg #f #H elim (pn_split g1) * #f1 #H1
[ elim (coafter_inv_pxp … Hg … H1 H) -g
  /3 width=5 by or_introl, ex3_2_intro/
| /4 width=5 by coafter_inv_nxp, or_intror, ex2_intro/
]
qed-.

lemma coafter_inv_pxx: ∀g1,g2,g. g1 ~⊚ g2 ≡ g → ∀f1. ↑f1 = g1 →
                       (∃∃f2,f. f1 ~⊚ f2 ≡ f & ↑f2 = g2 & ↑f = g) ∨
                       (∃∃f2,f. f1 ~⊚ f2 ≡ f & ⫯f2 = g2 & ⫯f = g).
#g1 #g2 #g #Hg #f1 #H1 elim (pn_split g2) * #f2 #H2
[ elim (coafter_inv_ppx … Hg … H1 H2) -g1
  /3 width=5 by or_introl, ex3_2_intro/
| elim (coafter_inv_pnx … Hg … H1 H2) -g1
  /3 width=5 by or_intror, ex3_2_intro/
]
qed-.

(* Basic properties *********************************************************)

corec lemma coafter_eq_repl_back2: ∀f1,f. eq_repl_back (λf2. f2 ~⊚ f1 ≡ f).
#f1 #f #f2 * -f2 -f1 -f
#f21 #f1 #f #g21 [1,2: #g1 ] #g #Hf #H21 [1,2: #H1 ] #H #g22 #H0
[ cases (eq_inv_px …  H0 …  H21) -g21 /3 width=7 by coafter_refl/
| cases (eq_inv_px …  H0 …  H21) -g21 /3 width=7 by coafter_push/
| cases (eq_inv_nx …  H0 …  H21) -g21 /3 width=5 by coafter_next/
]
qed-.

lemma coafter_eq_repl_fwd2: ∀f1,f. eq_repl_fwd (λf2. f2 ~⊚ f1 ≡ f).
#f1 #f @eq_repl_sym /2 width=3 by coafter_eq_repl_back2/
qed-.

corec lemma coafter_eq_repl_back1: ∀f2,f. eq_repl_back (λf1. f2 ~⊚ f1 ≡ f).
#f2 #f #f1 * -f2 -f1 -f
#f2 #f11 #f #g2 [1,2: #g11 ] #g #Hf #H2 [1,2: #H11 ] #H #g2 #H0
[ cases (eq_inv_px …  H0 …  H11) -g11 /3 width=7 by coafter_refl/
| cases (eq_inv_nx …  H0 …  H11) -g11 /3 width=7 by coafter_push/
| @(coafter_next … H2 H) /2 width=5 by/
]
qed-.

lemma coafter_eq_repl_fwd1: ∀f2,f. eq_repl_fwd (λf1. f2 ~⊚ f1 ≡ f).
#f2 #f @eq_repl_sym /2 width=3 by coafter_eq_repl_back1/
qed-.

corec lemma coafter_eq_repl_back0: ∀f1,f2. eq_repl_back (λf. f2 ~⊚ f1 ≡ f).
#f2 #f1 #f * -f2 -f1 -f
#f2 #f1 #f01 #g2 [1,2: #g1 ] #g01 #Hf01 #H2 [1,2: #H1 ] #H01 #g02 #H0
[ cases (eq_inv_px …  H0 …  H01) -g01 /3 width=7 by coafter_refl/
| cases (eq_inv_nx …  H0 …  H01) -g01 /3 width=7 by coafter_push/
| cases (eq_inv_px …  H0 …  H01) -g01 /3 width=5 by coafter_next/
]
qed-.

lemma coafter_eq_repl_fwd0: ∀f2,f1. eq_repl_fwd (λf. f2 ~⊚ f1 ≡ f).
#f2 #f1 @eq_repl_sym /2 width=3 by coafter_eq_repl_back0/
qed-.

(* Main inversion lemmas ****************************************************)

corec theorem coafter_mono: ∀f1,f2,x,y. f1 ~⊚ f2 ≡ x → f1 ~⊚ f2 ≡ y → x ≗ y.
#f1 #f2 #x #y * -f1 -f2 -x
#f1 #f2 #x #g1 [1,2: #g2 ] #g #Hx #H1 [1,2: #H2 ] #H0x #Hy
[ cases (coafter_inv_ppx … Hy … H1 H2) -g1 -g2 /3 width=8 by eq_push/
| cases (coafter_inv_pnx … Hy … H1 H2) -g1 -g2 /3 width=8 by eq_next/
| cases (coafter_inv_nxx … Hy … H1) -g1 /3 width=8 by eq_push/
]
qed-.

lemma coafter_mono_eq: ∀f1,f2,f. f1 ~⊚ f2 ≡ f → ∀g1,g2,g. g1 ~⊚ g2 ≡ g →
                       f1 ≗ g1 → f2 ≗ g2 → f ≗ g.
/4 width=4 by coafter_mono, coafter_eq_repl_back1, coafter_eq_repl_back2/ qed-.

(* Inversion lemmas with pushs **********************************************)

lemma coafter_fwd_pushs: ∀n,g2,g1,g. g2 ~⊚ g1 ≡ g → @⦃0, g2⦄ ≡ n →
                         ∃f. ↑*[n]f = g.
#n elim n -n /2 width=2 by ex_intro/
#n #IH #g2 #g1 #g #Hg #Hg2
cases (at_inv_pxn … Hg2) -Hg2 [ |*: // ] #f2 #Hf2 #H2
cases (coafter_inv_nxx … Hg … H2) -Hg -H2 #f #Hf #H0 destruct
elim (IH … Hf Hf2) -g1 -g2 -f2 /2 width=2 by ex_intro/
qed-.

(* Inversion lemmas with tail ***********************************************)

lemma coafter_inv_tl1: ∀g2,g1,g. g2 ~⊚ ⫱g1 ≡ g →
                       ∃∃f. ↑g2 ~⊚ g1 ≡ f & ⫱f = g.
#g2 #g1 #g elim (pn_split g1) * #f1 #H1 #H destruct
[ /3 width=7 by coafter_refl, ex2_intro/
| @(ex2_intro … (⫯g)) /2 width=7 by coafter_push/ (**) (* full auto fails *)
]
qed-.

lemma coafter_inv_tl0: ∀g2,g1,g. g2 ~⊚ g1 ≡ ⫱g →
                       ∃∃f1. ↑g2 ~⊚ f1 ≡ g & ⫱f1 = g1.
#g2 #g1 #g elim (pn_split g) * #f #H0 #H destruct
[ /3 width=7 by coafter_refl, ex2_intro/
| @(ex2_intro … (⫯g1)) /2 width=7 by coafter_push/ (**) (* full auto fails *)
]
qed-.

(* Properties with iterated tail ********************************************)

lemma coafter_tls: ∀n,f1,f2,f. @⦃0, f1⦄ ≡ n →
                   f1 ~⊚ f2 ≡ f → ⫱*[n]f1 ~⊚ f2 ≡ ⫱*[n]f.
#n elim n -n //
#n #IH #f1 #f2 #f #Hf1 #Hf
cases (at_inv_pxn … Hf1) -Hf1 [ |*: // ] #g1 #Hg1 #H1
cases (coafter_inv_nxx … Hf … H1) -Hf #g #Hg #H0 destruct
<tls_xn <tls_xn /2 width=1 by/
qed.

lemma coafter_tls_succ: ∀g2,g1,g. g2 ~⊚ g1 ≡ g →
                        ∀n. @⦃0, g2⦄ ≡ n → ⫱*[⫯n]g2 ~⊚ ⫱g1 ≡ ⫱*[⫯n]g.
#g2 #g1 #g #Hg #n #Hg2
lapply (coafter_tls … Hg2 … Hg) -Hg #Hg
lapply (at_pxx_tls … Hg2) -Hg2 #H
elim (at_inv_pxp … H) -H [ |*: // ] #f2 #H2
elim (coafter_inv_pxx … Hg … H2) -Hg * #f1 #f #Hf #H1 #H0 destruct
<tls_S <tls_S <H2 <H0 -g2 -g -n //
qed.

lemma coafter_fwd_xpx_pushs: ∀g2,f1,g,n. g2 ~⊚ ↑f1 ≡ g → @⦃0, g2⦄ ≡ n →
                             ∃f. ↑*[⫯n]f = g.
#g2 #g1 #g #n #Hg #Hg2
elim (coafter_fwd_pushs … Hg Hg2) #f #H0 destruct
lapply (coafter_tls … Hg2 Hg) -Hg <tls_pushs #Hf
lapply (at_pxx_tls … Hg2) -Hg2 #H
elim (at_inv_pxp … H) -H [ |*: // ] #f2 #H2
elim (coafter_inv_pxx … Hf … H2) -Hf -H2 * #f1 #g #_ #H1 #H0 destruct
[ /2 width=2 by ex_intro/
| elim (discr_next_push … H1)
] 
qed-.

lemma coafter_fwd_xnx_pushs: ∀g2,f1,g,n. g2 ~⊚ ⫯f1 ≡ g → @⦃0, g2⦄ ≡ n →
                             ∃f. ↑*[n] ⫯f = g.
#g2 #g1 #g #n #Hg #Hg2
elim (coafter_fwd_pushs … Hg Hg2) #f #H0 destruct
lapply (coafter_tls … Hg2 Hg) -Hg <tls_pushs #Hf
lapply (at_pxx_tls … Hg2) -Hg2 #H
elim (at_inv_pxp … H) -H [ |*: // ] #f2 #H2
elim (coafter_inv_pxx … Hf … H2) -Hf -H2 * #f1 #g #_ #H1 #H0 destruct
[ elim (discr_push_next … H1)
| /2 width=2 by ex_intro/
] 
qed-.

(* Properties with test for identity ****************************************)

corec lemma coafter_isid_sn: ∀f1. 𝐈⦃f1⦄ → ∀f2. f1 ~⊚ f2 ≡ f2.
#f1 * -f1 #f1 #g1 #Hf1 #H1 #f2 cases (pn_split f2) * #g2 #H2
/3 width=7 by coafter_push, coafter_refl/
qed.

corec lemma coafter_isid_dx: ∀f2,f. 𝐈⦃f2⦄ → 𝐈⦃f⦄ → ∀f1. f1 ~⊚ f2 ≡ f.
#f2 #f * -f2 #f2 #g2 #Hf2 #H2 * -f #f #g #Hf #H #f1 cases (pn_split f1) * #g1 #H1
[ /3 width=7 by coafter_refl/
| @(coafter_next … H1 … H) /3 width=3 by isid_push/
]
qed.

(* Inversion lemmas with test for identity **********************************)

lemma coafter_isid_inv_sn: ∀f1,f2,f. f1 ~⊚ f2 ≡ f → 𝐈⦃f1⦄ → f2 ≗ f.
/3 width=6 by coafter_isid_sn, coafter_mono/ qed-.

lemma coafter_isid_inv_dx: ∀f1,f2,f. f1 ~⊚ f2 ≡ f → 𝐈⦃f2⦄ → 𝐈⦃f⦄.
/4 width=4 by eq_id_isid, coafter_isid_dx, coafter_mono/ qed-.

(* Properties with test for uniform relocations *****************************)

lemma coafter_isuni_isid: ∀f2. 𝐈⦃f2⦄ → ∀f1. 𝐔⦃f1⦄ → f1 ~⊚ f2 ≡ f2.
#f #Hf #g #H elim H -g
/3 width=5 by coafter_isid_sn, coafter_eq_repl_back0, coafter_next, eq_push_inv_isid/
qed.


(*
lemma coafter_isid_isuni: ∀f1,f2. 𝐈⦃f2⦄ → 𝐔⦃f1⦄ → f1 ~⊚ ⫯f2 ≡ ⫯f1.
#f1 #f2 #Hf2 #H elim H -H
/5 width=7 by coafter_isid_dx, coafter_eq_repl_back2, coafter_next, coafter_push, eq_push_inv_isid/
qed.

lemma coafter_uni_next2: ∀f2. 𝐔⦃f2⦄ → ∀f1,f. ⫯f2 ~⊚ f1 ≡ f → f2 ~⊚ ⫯f1 ≡ f.
#f2 #H elim H -f2
[ #f2 #Hf2 #f1 #f #Hf
  elim (coafter_inv_nxx … Hf) -Hf [2,3: // ] #g #Hg #H0 destruct
  /4 width=7 by coafter_isid_inv_sn, coafter_isid_sn, coafter_eq_repl_back0, eq_next/
| #f2 #_ #g2 #H2 #IH #f1 #f #Hf
  elim (coafter_inv_nxx … Hf) -Hf [2,3: // ] #g #Hg #H0 destruct
  /3 width=5 by coafter_next/
]
qed.
*)

(* Properties with uniform relocations **************************************)

lemma coafter_uni_sn: ∀i,f. 𝐔❴i❵ ~⊚ f ≡ ↑*[i] f.
#i elim i -i /2 width=5 by coafter_isid_sn, coafter_next/
qed.

(*
lemma coafter_uni: ∀n1,n2. 𝐔❴n1❵ ~⊚ 𝐔❴n2❵ ≡ 𝐔❴n1+n2❵.
@nat_elim2
/4 width=5 by coafter_uni_next2, coafter_isid_sn, coafter_isid_dx, coafter_next/
qed.

(* Forward lemmas on at *****************************************************)

lemma coafter_at_fwd: ∀i,i1,f. @⦃i1, f⦄ ≡ i → ∀f2,f1. f2 ~⊚ f1 ≡ f →
                      ∃∃i2. @⦃i1, f1⦄ ≡ i2 & @⦃i2, f2⦄ ≡ i.
#i elim i -i [2: #i #IH ] #i1 #f #Hf #f2 #f1 #Hf21
[ elim (at_inv_xxn … Hf) -Hf [1,3:* |*: // ]
  [1: #g #j1 #Hg #H0 #H |2,4: #g #Hg #H ]
| elim (at_inv_xxp … Hf) -Hf //
  #g #H1 #H
]
[2: elim (coafter_inv_xxn … Hf21 … H) -f *
    [ #g2 #g1 #Hg21 #H2 #H1 | #g2 #Hg21 #H2 ]
|*: elim (coafter_inv_xxp … Hf21 … H) -f
    #g2 #g1 #Hg21 #H2 #H1
]
[4: -Hg21 |*: elim (IH … Hg … Hg21) -g -IH ]
/3 width=9 by at_refl, at_push, at_next, ex2_intro/
qed-.

lemma coafter_fwd_at: ∀i,i2,i1,f1,f2. @⦃i1, f1⦄ ≡ i2 → @⦃i2, f2⦄ ≡ i →
                      ∀f. f2 ~⊚ f1 ≡ f → @⦃i1, f⦄ ≡ i.
#i elim i -i [2: #i #IH ] #i2 #i1 #f1 #f2 #Hf1 #Hf2 #f #Hf
[ elim (at_inv_xxn … Hf2) -Hf2 [1,3: * |*: // ]
  #g2 [ #j2 ] #Hg2 [ #H22 ] #H20
  [ elim (at_inv_xxn … Hf1 … H22) -i2 *
    #g1 [ #j1 ] #Hg1 [ #H11 ] #H10
    [ elim (coafter_inv_ppx … Hf … H20 H10) -f1 -f2 /3 width=7 by at_push/
    | elim (coafter_inv_pnx … Hf … H20 H10) -f1 -f2 /3 width=6 by at_next/
    ]
  | elim (coafter_inv_nxx … Hf … H20) -f2 /3 width=7 by at_next/
  ]
| elim (at_inv_xxp … Hf2) -Hf2 // #g2 #H22 #H20
  elim (at_inv_xxp … Hf1 … H22) -i2 #g1 #H11 #H10
  elim (coafter_inv_ppx … Hf … H20 H10) -f1 -f2 /2 width=2 by at_refl/
]
qed-.

lemma coafter_fwd_at2: ∀f,i1,i. @⦃i1, f⦄ ≡ i → ∀f1,i2. @⦃i1, f1⦄ ≡ i2 →
                       ∀f2. f2 ~⊚ f1 ≡ f → @⦃i2, f2⦄ ≡ i.
#f #i1 #i #Hf #f1 #i2 #Hf1 #f2 #H elim (coafter_at_fwd … Hf … H) -f
#j1 #H #Hf2 <(at_mono … Hf1 … H) -i1 -i2 //
qed-.

lemma coafter_fwd_at1: ∀i,i2,i1,f,f2. @⦃i1, f⦄ ≡ i → @⦃i2, f2⦄ ≡ i →
                       ∀f1. f2 ~⊚ f1 ≡ f → @⦃i1, f1⦄ ≡ i2.
#i elim i -i [2: #i #IH ] #i2 #i1 #f #f2 #Hf #Hf2 #f1 #Hf1
[ elim (at_inv_xxn … Hf) -Hf [1,3: * |*: // ]
  #g [ #j1 ] #Hg [ #H01 ] #H00
  elim (at_inv_xxn … Hf2) -Hf2 [1,3,5,7: * |*: // ]
  #g2 [1,3: #j2 ] #Hg2 [1,2: #H22 ] #H20
  [ elim (coafter_inv_pxp … Hf1 … H20 H00) -f2 -f /3 width=7 by at_push/
  | elim (coafter_inv_pxn … Hf1 … H20 H00) -f2 -f /3 width=5 by at_next/
  | elim (coafter_inv_nxp … Hf1 … H20 H00)
  | /4 width=9 by coafter_inv_nxn, at_next/
  ]
| elim (at_inv_xxp … Hf) -Hf // #g #H01 #H00
  elim (at_inv_xxp … Hf2) -Hf2 // #g2 #H21 #H20
  elim (coafter_inv_pxp … Hf1 … H20 H00) -f2 -f /3 width=2 by at_refl/
]
qed-.

(* Properties with at *******************************************************)

lemma coafter_uni_dx: ∀i2,i1,f2. @⦃i1, f2⦄ ≡ i2 →
                      ∀f. f2 ~⊚ 𝐔❴i1❵ ≡ f → 𝐔❴i2❵ ~⊚ ⫱*[i2] f2 ≡ f.
#i2 elim i2 -i2
[ #i1 #f2 #Hf2 #f #Hf
  elim (at_inv_xxp … Hf2) -Hf2 // #g2 #H1 #H2 destruct
  lapply (coafter_isid_inv_dx … Hf ?) -Hf
  /3 width=3 by coafter_isid_sn, coafter_eq_repl_back0/
| #i2 #IH #i1 #f2 #Hf2 #f #Hf
  elim (at_inv_xxn … Hf2) -Hf2 [1,3: * |*: // ]
  [ #g2 #j1 #Hg2 #H1 #H2 destruct
    elim (coafter_inv_pnx … Hf) -Hf [ |*: // ] #g #Hg #H destruct
    /3 width=5 by coafter_next/
  | #g2 #Hg2 #H2 destruct
    elim (coafter_inv_nxx … Hf) -Hf [2,3: // ] #g #Hg #H destruct
    /3 width=5 by coafter_next/
  ]
]
qed.

lemma coafter_uni_sn: ∀i2,i1,f2. @⦃i1, f2⦄ ≡ i2 →
                      ∀f. 𝐔❴i2❵ ~⊚ ⫱*[i2] f2 ≡ f → f2 ~⊚ 𝐔❴i1❵ ≡ f.
#i2 elim i2 -i2
[ #i1 #f2 #Hf2 #f #Hf
  elim (at_inv_xxp … Hf2) -Hf2 // #g2 #H1 #H2 destruct
  lapply (coafter_isid_inv_sn … Hf ?) -Hf
  /3 width=3 by coafter_isid_dx, coafter_eq_repl_back0/
| #i2 #IH #i1 #f2 #Hf2 #f #Hf
  elim (coafter_inv_nxx … Hf) -Hf [2,3: // ] #g #Hg #H destruct
  elim (at_inv_xxn … Hf2) -Hf2 [1,3: * |*: // ]
  [ #g2 #j1 #Hg2 #H1 #H2 destruct /3 width=7 by coafter_push/
  | #g2 #Hg2 #H2 destruct /3 width=5 by coafter_next/
  ]
]
qed-.

lemma coafter_uni_succ_dx: ∀i2,i1,f2. @⦃i1, f2⦄ ≡ i2 →
                           ∀f. f2 ~⊚ 𝐔❴⫯i1❵ ≡ f → 𝐔❴⫯i2❵ ~⊚ ⫱*[⫯i2] f2 ≡ f.
#i2 elim i2 -i2
[ #i1 #f2 #Hf2 #f #Hf
  elim (at_inv_xxp … Hf2) -Hf2 // #g2 #H1 #H2 destruct
  elim (coafter_inv_pnx … Hf) -Hf [ |*: // ] #g #Hg #H
  lapply (coafter_isid_inv_dx … Hg ?) -Hg
  /4 width=5 by coafter_isid_sn, coafter_eq_repl_back0, coafter_next/
| #i2 #IH #i1 #f2 #Hf2 #f #Hf
  elim (at_inv_xxn … Hf2) -Hf2 [1,3: * |*: // ]
  [ #g2 #j1 #Hg2 #H1 #H2 destruct
    elim (coafter_inv_pnx … Hf) -Hf [ |*: // ] #g #Hg #H destruct
    /3 width=5 by coafter_next/
  | #g2 #Hg2 #H2 destruct
    elim (coafter_inv_nxx … Hf) -Hf [2,3: // ] #g #Hg #H destruct
    /3 width=5 by coafter_next/
  ]
]
qed.

lemma coafter_uni_succ_sn: ∀i2,i1,f2. @⦃i1, f2⦄ ≡ i2 →
                           ∀f. 𝐔❴⫯i2❵ ~⊚ ⫱*[⫯i2] f2 ≡ f → f2 ~⊚ 𝐔❴⫯i1❵ ≡ f.
#i2 elim i2 -i2
[ #i1 #f2 #Hf2 #f #Hf
  elim (at_inv_xxp … Hf2) -Hf2 // #g2 #H1 #H2 destruct
  elim (coafter_inv_nxx … Hf) -Hf [ |*: // ] #g #Hg #H destruct
  lapply (coafter_isid_inv_sn … Hg ?) -Hg
  /4 width=7 by coafter_isid_dx, coafter_eq_repl_back0, coafter_push/
| #i2 #IH #i1 #f2 #Hf2 #f #Hf
  elim (coafter_inv_nxx … Hf) -Hf [2,3: // ] #g #Hg #H destruct
  elim (at_inv_xxn … Hf2) -Hf2 [1,3: * |*: // ]
  [ #g2 #j1 #Hg2 #H1 #H2 destruct <tls_xn in Hg; /3 width=7 by coafter_push/
  | #g2 #Hg2 #H2 destruct <tls_xn in Hg; /3 width=5 by coafter_next/
  ]
]
qed-.

lemma coafter_uni_one_dx: ∀f2,f. ↑f2 ~⊚ 𝐔❴⫯O❵ ≡ f → 𝐔❴⫯O❵ ~⊚ f2 ≡ f.
#f2 #f #H @(coafter_uni_succ_dx … (↑f2)) /2 width=3 by at_refl/
qed.

lemma coafter_uni_one_sn: ∀f1,f. 𝐔❴⫯O❵ ~⊚ f1 ≡ f → ↑f1 ~⊚ 𝐔❴⫯O❵ ≡ f.
/3 width=3 by coafter_uni_succ_sn, at_refl/ qed-.
*)
(* Forward lemmas with istot ************************************************)
(*
lemma coafter_istot_fwd: ∀f2,f1,f. f2 ~⊚ f1 ≡ f → 𝐓⦃f2⦄ → 𝐓⦃f1⦄ → 𝐓⦃f⦄.
#f2 #f1 #f #Hf #Hf2 #Hf1 #i1 elim (Hf1 i1) -Hf1
#i2 #Hf1 elim (Hf2 i2) -Hf2
/3 width=7 by coafter_fwd_at, ex_intro/
qed-.

lemma coafter_fwd_istot_dx: ∀f2,f1,f. f2 ~⊚ f1 ≡ f → 𝐓⦃f⦄ → 𝐓⦃f1⦄.
#f2 #f1 #f #H #Hf #i1 elim (Hf i1) -Hf
#i2 #Hf elim (coafter_at_fwd … Hf … H) -f /2 width=2 by ex_intro/
qed-.

lemma coafter_fwd_istot_sn: ∀f2,f1,f. f2 ~⊚ f1 ≡ f → 𝐓⦃f⦄ → 𝐓⦃f2⦄.
#f2 #f1 #f #H #Hf #i1 elim (Hf i1) -Hf
#i #Hf elim (coafter_at_fwd … Hf … H) -f
#i2 #Hf1 #Hf2 lapply (at_increasing … Hf1) -f1
#Hi12 elim (at_le_ex … Hf2 … Hi12) -i2 /2 width=2 by ex_intro/
qed-.

lemma coafter_inv_istot: ∀f2,f1,f. f2 ~⊚ f1 ≡ f → 𝐓⦃f⦄ → 𝐓⦃f2⦄ ∧ 𝐓⦃f1⦄.
/3 width=4 by coafter_fwd_istot_sn, coafter_fwd_istot_dx, conj/ qed-.

lemma coafter_at1_fwd: ∀f1,i1,i2. @⦃i1, f1⦄ ≡ i2 → ∀f2. 𝐓⦃f2⦄ → ∀f. f2 ~⊚ f1 ≡ f →
                     ∃∃i. @⦃i2, f2⦄ ≡ i & @⦃i1, f⦄ ≡ i.
#f1 #i1 #i2 #Hf1 #f2 #Hf2 #f #Hf elim (Hf2 i2) -Hf2
/3 width=8 by coafter_fwd_at, ex2_intro/
qed-.

lemma coafter_fwd_isid_sn: ∀f2,f1,f. 𝐓⦃f⦄ → f2 ~⊚ f1 ≡ f → f1 ≗ f → 𝐈⦃f2⦄.
#f2 #f1 #f #H #Hf elim (coafter_inv_istot … Hf H) -H
#Hf2 #Hf1 #H @isid_at_total // -Hf2
#i2 #i #Hf2 elim (Hf1 i2) -Hf1
#i0 #Hf1 lapply (at_increasing … Hf1)
#Hi20 lapply (coafter_fwd_at2 … i0 … Hf1 … Hf) -Hf
/3 width=7 by at_eq_repl_back, at_mono, at_id_le/
qed-.

lemma coafter_fwd_isid_dx: ∀f2,f1,f.  𝐓⦃f⦄ → f2 ~⊚ f1 ≡ f → f2 ≗ f → 𝐈⦃f1⦄.
#f2 #f1 #f #H #Hf elim (coafter_inv_istot … Hf H) -H
#Hf2 #Hf1 #H2 @isid_at_total // -Hf1
#i1 #i2 #Hi12 elim (coafter_at1_fwd … Hi12 … Hf) -f1
/3 width=8 by at_inj, at_eq_repl_back/
qed-.
*)
corec fact coafter_inj_O_aux: ∀f1. @⦃0, f1⦄ ≡ 0 → H_coafter_inj f1.
#f1 #H1f1 #H2f1 #f #f21 #f22 #H1f #H2f
cases (at_inv_pxp … H1f1) -H1f1 [ |*: // ] #g1 #H1
lapply (istot_inv_push … H2f1 … H1) -H2f1 #H2g1
cases (H2g1 0) #n #Hn
cases (coafter_inv_pxx … H1f … H1) -H1f * #g21 #g #H1g #H21 #H
[ cases (coafter_inv_pxp … H2f … H1 H) -f1 -f #g22 #H2g #H22
  @(eq_push … H21 H22) -f21 -f22
| cases (coafter_inv_pxn … H2f … H1 H) -f1 -f #g22 #H2g #H22
  @(eq_next … H21 H22) -f21 -f22
]
@(coafter_inj_O_aux (⫱*[n]g1) … (⫱*[n]g)) -coafter_inj_O_aux
/2 width=1 by coafter_tls, istot_tls, at_pxx_tls/
qed-.

fact coafter_inj_aux: (∀f1. @⦃0, f1⦄ ≡ 0 → H_coafter_inj f1) →
                      ∀i2,f1. @⦃0, f1⦄ ≡ i2 → H_coafter_inj f1.
#H0 #i2 elim i2 -i2 /2 width=1 by/ -H0
#i2 #IH #f1 #H1f1 #H2f1 #f #f21 #f22 #H1f #H2f
elim (at_inv_pxn … H1f1) -H1f1 [ |*: // ] #g1 #H1g1 #H1
elim (coafter_inv_nxx … H1f … H1) -H1f #g #H1g #H
lapply (coafter_inv_nxp … H2f … H1 H) -f #H2g
/3 width=6 by istot_inv_next/
qed-.

theorem coafter_inj: ∀f1. H_coafter_inj f1.
#f1 #H cases (H 0) /3 width=7 by coafter_inj_aux, coafter_inj_O_aux/
qed-.

corec fact coafter_fwd_isid2_O_aux: ∀f1. @⦃0, f1⦄ ≡ 0 →
                                    H_coafter_fwd_isid2 f1.
#f1 #H1f1 #f2 #f #H #H2f1 #Hf
cases (at_inv_pxp … H1f1) -H1f1 [ |*: // ] #g1 #H1
lapply (istot_inv_push … H2f1 … H1) -H2f1 #H2g1
cases (H2g1 0) #n #Hn
cases (coafter_inv_pxx … H … H1) -H * #g2 #g #H #H2 #H0
[ lapply (isid_inv_push … Hf … H0) -Hf #Hg
  @(isid_push … H2)
  /3 width=7 by coafter_tls, istot_tls, at_pxx_tls, isid_tls/
| cases (isid_inv_next … Hf … H0)
]
qed-.

fact coafter_fwd_isid2_aux: (∀f1. @⦃0, f1⦄ ≡ 0 → H_coafter_fwd_isid2 f1) →
                            ∀i2,f1. @⦃0, f1⦄ ≡ i2 → H_coafter_fwd_isid2 f1.
#H0 #i2 elim i2 -i2 /2 width=1 by/ -H0
#i2 #IH #f1 #H1f1 #f2 #f #H #H2f1 #Hf
elim (at_inv_pxn … H1f1) -H1f1 [ |*: // ] #g1 #Hg1 #H1
elim (coafter_inv_nxx … H … H1) -H #g #Hg #H0
@(IH … Hg1 … Hg) /2 width=3 by istot_inv_next, isid_inv_push/ (**) (* full auto fails *)
qed-.

lemma coafter_fwd_isid2: ∀f1. H_coafter_fwd_isid2 f1.
#f1 #f2 #f #Hf #H cases (H 0)
/3 width=7 by coafter_fwd_isid2_aux, coafter_fwd_isid2_O_aux/
qed-.

fact coafter_isfin2_fwd_O_aux: ∀f1. @⦃0, f1⦄ ≡ 0 →
                               H_coafter_isfin2_fwd f1.
#f1 #Hf1 #f2 #H
generalize in match Hf1; generalize in match f1; -f1
@(isfin_ind … H) -f2
[ /3 width=4 by coafter_isid_inv_dx, isfin_isid/ ]
#f2 #_ #IH #f1 #H #Hf1 #f #Hf
elim (at_inv_pxp … H) -H [ |*: // ] #g1 #H1
lapply (istot_inv_push … Hf1 … H1) -Hf1 #Hg1
elim (Hg1 0) #n #Hn
[ elim (coafter_inv_ppx … Hf) | elim (coafter_inv_pnx … Hf)
] -Hf [1,6: |*: // ] #g #Hg #H0 destruct
/5 width=6 by isfin_next, isfin_push, isfin_inv_tls, istot_tls, at_pxx_tls, coafter_tls/
qed-.

fact coafter_isfin2_fwd_aux: (∀f1. @⦃0, f1⦄ ≡ 0 → H_coafter_isfin2_fwd f1) →
                             ∀i2,f1. @⦃0, f1⦄ ≡ i2 → H_coafter_isfin2_fwd f1.
#H0 #i2 elim i2 -i2 /2 width=1 by/ -H0
#i2 #IH #f1 #H1f1 #f2 #Hf2 #H2f1 #f #Hf
elim (at_inv_pxn … H1f1) -H1f1 [ |*: // ] #g1 #Hg1 #H1
elim (coafter_inv_nxx … Hf … H1) -Hf #g #Hg #H0
lapply (IH … Hg1 … Hg) -i2 -Hg
/2 width=4 by istot_inv_next, isfin_push/ (**) (* full auto fails *)
qed-.

lemma coafter_isfin2_fwd: ∀f1. H_coafter_isfin2_fwd f1.
#f1 #f2 #Hf2 #Hf1 cases (Hf1 0)
/3 width=7 by coafter_isfin2_fwd_aux, coafter_isfin2_fwd_O_aux/
qed-.

lemma coafter_inv_sor: ∀f. 𝐅⦃f⦄ → ∀f2. 𝐓⦃f2⦄ → ∀f1. f2 ~⊚ f1 ≡ f → ∀fa,fb. fa ⋓ fb ≡ f →
                       ∃∃f1a,f1b. f2 ~⊚ f1a ≡ fa & f2 ~⊚ f1b ≡ fb & f1a ⋓ f1b ≡ f1.
@isfin_ind
[ #f #Hf #f2 #Hf2 #f1 #H1f #fa #fb #H2f
  elim (sor_inv_isid3 … H2f) -H2f //
  lapply (coafter_fwd_isid2 … H1f ??) -H1f //
  /3 width=5 by ex3_2_intro, coafter_isid_dx, sor_isid/
| #f #_ #IH #f2 #Hf2 #f1 #H1 #fa #fb #H2
  elim (sor_inv_xxp … H2) -H2 [ |*: // ] #ga #gb #H2f
  elim (coafter_inv_xxp … H1) -H1 [1,3: * |*: // ] #g2 [ #g1 ] #H1f #Hgf2
  [ lapply (istot_inv_push … Hf2 … Hgf2) | lapply (istot_inv_next … Hf2 … Hgf2) ] -Hf2 #Hg2
  elim (IH … Hg2 … H1f … H2f) -f -Hg2
  /3 width=11 by sor_pp, ex3_2_intro, coafter_refl, coafter_next/
| #f #_ #IH #f2 #Hf2 #f1 #H1 #fa #fb #H2
  elim (coafter_inv_xxn … H1) -H1 [ |*: // ] #g2 #g1 #H1f #Hgf2
  lapply (istot_inv_push … Hf2 … Hgf2) -Hf2 #Hg2
  elim (sor_inv_xxn … H2) -H2 [1,3,4: * |*: // ] #ga #gb #H2f
  elim (IH … Hg2 … H1f … H2f) -f -Hg2
  /3 width=11 by sor_np, sor_pn, sor_nn, ex3_2_intro, coafter_refl, coafter_push/
]
qed-.

(* Properties with istot ****************************************************)

lemma coafter_sor: ∀f. 𝐅⦃f⦄ → ∀f2. 𝐓⦃f2⦄ → ∀f1. f2 ~⊚ f1 ≡ f → ∀f1a,f1b. f1a ⋓ f1b ≡ f1 →
                   ∃∃fa,fb. f2 ~⊚ f1a ≡ fa & f2 ~⊚ f1b ≡ fb & fa ⋓ fb ≡ f.
@isfin_ind
[ #f #Hf #f2 #Hf2 #f1 #Hf #f1a #f1b #Hf1
  lapply (coafter_fwd_isid2 … Hf ??) -Hf // #H2f1
  elim (sor_inv_isid3 … Hf1) -Hf1 //
  /3 width=5 by coafter_isid_dx, sor_refl, ex3_2_intro/
| #f #_ #IH #f2 #Hf2 #f1 #H1 #f1a #f1b #H2
  elim (coafter_inv_xxp … H1) -H1 [1,3: * |*: // ]
  [ #g2 #g1 #Hf #Hgf2 #Hgf1
    elim (sor_inv_xxp … H2) -H2 [ |*: // ] #ga #gb #Hg1
    lapply (istot_inv_push … Hf2 … Hgf2) -Hf2 #Hg2
    elim (IH … Hf … Hg1) // -f1 -g1 -IH -Hg2
    /3 width=11 by coafter_refl, sor_pp, ex3_2_intro/
  | #g2 #Hf #Hgf2
    lapply (istot_inv_next … Hf2 … Hgf2) -Hf2 #Hg2
    elim (IH … Hf … H2) // -f1 -IH -Hg2
    /3 width=11 by coafter_next, sor_pp, ex3_2_intro/
  ]
| #f #_ #IH #f2 #Hf2 #f1 #H1 #f1a #f1b #H2
  elim (coafter_inv_xxn … H1) -H1 [ |*: // ] #g2 #g1 #Hf #Hgf2 #Hgf1
  lapply (istot_inv_push … Hf2 … Hgf2) -Hf2 #Hg2
  elim (sor_inv_xxn … H2) -H2 [1,3,4: * |*: // ] #ga #gb #Hg1
  elim (IH … Hf … Hg1) // -f1 -g1 -IH -Hg2
  /3 width=11 by coafter_refl, coafter_push, sor_np, sor_pn, sor_nn, ex3_2_intro/
]
qed-.

(* Properties with after ****************************************************)
(*
corec theorem coafter_trans1: ∀f0,f3,f4. f0 ~⊚ f3 ≡ f4 →
                            ∀f1,f2. f1 ~⊚ f2 ≡ f0 →
                            ∀f. f2 ~⊚ f3 ≡ f → f1 ~⊚ f ≡ f4.
#f0 #f3 #f4 * -f0 -f3 -f4 #f0 #f3 #f4 #g0 [1,2: #g3 ] #g4
[ #Hf4 #H0 #H3 #H4 #g1 #g2 #Hg0 #g #Hg
  cases (coafter_inv_xxp … Hg0 … H0) -g0
  #f1 #f2 #Hf0 #H1 #H2
  cases (coafter_inv_ppx … Hg … H2 H3) -g2 -g3
  #f #Hf #H /3 width=7 by coafter_refl/
| #Hf4 #H0 #H3 #H4 #g1 #g2 #Hg0 #g #Hg
  cases (coafter_inv_xxp … Hg0 … H0) -g0
  #f1 #f2 #Hf0 #H1 #H2
  cases (coafter_inv_pnx … Hg … H2 H3) -g2 -g3
  #f #Hf #H /3 width=7 by coafter_push/
| #Hf4 #H0 #H4 #g1 #g2 #Hg0 #g #Hg
  cases (coafter_inv_xxn … Hg0 … H0) -g0 *
  [ #f1 #f2 #Hf0 #H1 #H2
    cases (coafter_inv_nxx … Hg … H2) -g2
    #f #Hf #H /3 width=7 by coafter_push/
  | #f1 #Hf0 #H1 /3 width=6 by coafter_next/
  ]
]
qed-.

corec theorem coafter_trans2: ∀f1,f0,f4. f1 ~⊚ f0 ≡ f4 →
                            ∀f2, f3. f2 ~⊚ f3 ≡ f0 →
                            ∀f. f1 ~⊚ f2 ≡ f → f ~⊚ f3 ≡ f4.
#f1 #f0 #f4 * -f1 -f0 -f4 #f1 #f0 #f4 #g1 [1,2: #g0 ] #g4
[ #Hf4 #H1 #H0 #H4 #g2 #g3 #Hg0 #g #Hg
  cases (coafter_inv_xxp … Hg0 … H0) -g0
  #f2 #f3 #Hf0 #H2 #H3
  cases (coafter_inv_ppx … Hg … H1 H2) -g1 -g2
  #f #Hf #H /3 width=7 by coafter_refl/
| #Hf4 #H1 #H0 #H4 #g2 #g3 #Hg0 #g #Hg
  cases (coafter_inv_xxn … Hg0 … H0) -g0 *
  [ #f2 #f3 #Hf0 #H2 #H3
    cases (coafter_inv_ppx … Hg … H1 H2) -g1 -g2
    #f #Hf #H /3 width=7 by coafter_push/
  | #f2 #Hf0 #H2
    cases (coafter_inv_pnx … Hg … H1 H2) -g1 -g2
    #f #Hf #H /3 width=6 by coafter_next/
  ]
| #Hf4 #H1 #H4 #f2 #f3 #Hf0 #g #Hg
  cases (coafter_inv_nxx … Hg … H1) -g1
  #f #Hg #H /3 width=6 by coafter_next/
]
qed-.
*)
