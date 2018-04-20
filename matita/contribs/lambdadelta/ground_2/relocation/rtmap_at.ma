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

include "ground_2/notation/relations/rat_3.ma".
include "ground_2/relocation/rtmap_uni.ma".

(* RELOCATION MAP ***********************************************************)

coinductive at: rtmap → relation nat ≝
| at_refl: ∀f,g,j1,j2. ⫯f = g → 0 = j1 → 0 = j2 → at g j1 j2 
| at_push: ∀f,i1,i2. at f i1 i2 → ∀g,j1,j2. ⫯f = g → ↑i1 = j1 → ↑i2 = j2 → at g j1 j2
| at_next: ∀f,i1,i2. at f i1 i2 → ∀g,j2. ↑f = g → ↑i2 = j2 → at g i1 j2
.

interpretation "relational application (rtmap)"
   'RAt i1 f i2 = (at f i1 i2).

definition H_at_div: relation4 rtmap rtmap rtmap rtmap ≝ λf2,g2,f1,g1.
                     ∀jf,jg,j. @⦃jf, f2⦄ ≘ j → @⦃jg, g2⦄ ≘ j →
                     ∃∃j0. @⦃j0, f1⦄ ≘ jf & @⦃j0, g1⦄ ≘ jg.

(* Basic inversion lemmas ***************************************************)

lemma at_inv_ppx: ∀f,i1,i2. @⦃i1, f⦄ ≘ i2 → ∀g. 0 = i1 → ⫯g = f → 0 = i2.
#f #i1 #i2 * -f -i1 -i2 //
[ #f #i1 #i2 #_ #g #j1 #j2 #_ * #_ #x #H destruct
| #f #i1 #i2 #_ #g #j2 * #_ #x #_ #H elim (discr_push_next … H)
]
qed-.

lemma at_inv_npx: ∀f,i1,i2. @⦃i1, f⦄ ≘ i2 → ∀g,j1. ↑j1 = i1 → ⫯g = f →
                  ∃∃j2. @⦃j1, g⦄ ≘ j2 & ↑j2 = i2.
#f #i1 #i2 * -f -i1 -i2
[ #f #g #j1 #j2 #_ * #_ #x #x1 #H destruct
| #f #i1 #i2 #Hi #g #j1 #j2 * * * #x #x1 #H #Hf >(injective_push … Hf) -g destruct /2 width=3 by ex2_intro/
| #f #i1 #i2 #_ #g #j2 * #_ #x #x1 #_ #H elim (discr_push_next … H)
]
qed-.

lemma at_inv_xnx: ∀f,i1,i2. @⦃i1, f⦄ ≘ i2 → ∀g. ↑g = f →
                  ∃∃j2. @⦃i1, g⦄ ≘ j2 & ↑j2 = i2.
#f #i1 #i2 * -f -i1 -i2
[ #f #g #j1 #j2 * #_ #_ #x #H elim (discr_next_push … H)
| #f #i1 #i2 #_ #g #j1 #j2 * #_ #_ #x #H elim (discr_next_push … H)
| #f #i1 #i2 #Hi #g #j2 * * #x #H >(injective_next … H) -g /2 width=3 by ex2_intro/
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma at_inv_ppn: ∀f,i1,i2. @⦃i1, f⦄ ≘ i2 →
                  ∀g,j2. 0 = i1 → ⫯g = f → ↑j2 = i2 → ⊥.
#f #i1 #i2 #Hf #g #j2 #H1 #H <(at_inv_ppx … Hf … H1 H) -f -g -i1 -i2
#H destruct
qed-.

lemma at_inv_npp: ∀f,i1,i2. @⦃i1, f⦄ ≘ i2 →
                  ∀g,j1. ↑j1 = i1 → ⫯g = f → 0 = i2 → ⊥.
#f #i1 #i2 #Hf #g #j1 #H1 #H elim (at_inv_npx … Hf … H1 H) -f -i1
#x2 #Hg * -i2 #H destruct
qed-.

lemma at_inv_npn: ∀f,i1,i2. @⦃i1, f⦄ ≘ i2 →
                  ∀g,j1,j2. ↑j1 = i1 → ⫯g = f → ↑j2 = i2 → @⦃j1, g⦄ ≘ j2.
#f #i1 #i2 #Hf #g #j1 #j2 #H1 #H elim (at_inv_npx … Hf … H1 H) -f -i1
#x2 #Hg * -i2 #H destruct //
qed-.

lemma at_inv_xnp: ∀f,i1,i2. @⦃i1, f⦄ ≘ i2 →
                  ∀g. ↑g = f → 0 = i2 → ⊥.
#f #i1 #i2 #Hf #g #H elim (at_inv_xnx … Hf … H) -f
#x2 #Hg * -i2 #H destruct
qed-.

lemma at_inv_xnn: ∀f,i1,i2. @⦃i1, f⦄ ≘ i2 →
                  ∀g,j2. ↑g = f → ↑j2 = i2 → @⦃i1, g⦄ ≘ j2.
#f #i1 #i2 #Hf #g #j2 #H elim (at_inv_xnx … Hf … H) -f
#x2 #Hg * -i2 #H destruct //
qed-.

lemma at_inv_pxp: ∀f,i1,i2. @⦃i1, f⦄ ≘ i2 → 0 = i1 → 0 = i2 → ∃g. ⫯g = f.
#f elim (pn_split … f) * /2 width=2 by ex_intro/
#g #H #i1 #i2 #Hf #H1 #H2 cases (at_inv_xnp … Hf … H H2)
qed-.

lemma at_inv_pxn: ∀f,i1,i2. @⦃i1, f⦄ ≘ i2 → ∀j2. 0 = i1 → ↑j2 = i2 →
                  ∃∃g. @⦃i1, g⦄ ≘ j2 & ↑g = f.
#f elim (pn_split … f) *
#g #H #i1 #i2 #Hf #j2 #H1 #H2
[ elim (at_inv_ppn … Hf … H1 H H2)
| /3 width=5 by at_inv_xnn, ex2_intro/
]
qed-.

lemma at_inv_nxp: ∀f,i1,i2. @⦃i1, f⦄ ≘ i2 →
                  ∀j1. ↑j1 = i1 → 0 = i2 → ⊥.
#f elim (pn_split f) *
#g #H #i1 #i2 #Hf #j1 #H1 #H2
[ elim (at_inv_npp … Hf … H1 H H2)
| elim (at_inv_xnp … Hf … H H2)
]
qed-.

lemma at_inv_nxn: ∀f,i1,i2. @⦃i1, f⦄ ≘ i2 → ∀j1,j2. ↑j1 = i1 → ↑j2 = i2 →
                  (∃∃g. @⦃j1, g⦄ ≘ j2 & ⫯g = f) ∨
                  ∃∃g. @⦃i1, g⦄ ≘ j2 & ↑g = f.
#f elim (pn_split f) *
/4 width=7 by at_inv_xnn, at_inv_npn, ex2_intro, or_intror, or_introl/
qed-.

(* Note: the following inversion lemmas must be checked *)
lemma at_inv_xpx: ∀f,i1,i2. @⦃i1, f⦄ ≘ i2 → ∀g. ⫯g = f →
                  (0 = i1 ∧ 0 = i2) ∨
                  ∃∃j1,j2. @⦃j1, g⦄ ≘ j2 & ↑j1 = i1 & ↑j2 = i2.
#f * [2: #i1 ] #i2 #Hf #g #H
[ elim (at_inv_npx … Hf … H) -f /3 width=5 by or_intror, ex3_2_intro/
| >(at_inv_ppx … Hf … H) -f /3 width=1 by conj, or_introl/
]
qed-.

lemma at_inv_xpp: ∀f,i1,i2. @⦃i1, f⦄ ≘ i2 → ∀g. ⫯g = f → 0 = i2 → 0 = i1.
#f #i1 #i2 #Hf #g #H elim (at_inv_xpx … Hf … H) -f * //
#j1 #j2 #_ #_ * -i2 #H destruct
qed-.

lemma at_inv_xpn: ∀f,i1,i2. @⦃i1, f⦄ ≘ i2 → ∀g,j2. ⫯g = f → ↑j2 = i2 →
                  ∃∃j1. @⦃j1, g⦄ ≘ j2 & ↑j1 = i1.
#f #i1 #i2 #Hf #g #j2 #H elim (at_inv_xpx … Hf … H) -f *
[ #_ * -i2 #H destruct
| #x1 #x2 #Hg #H1 * -i2 #H destruct /2 width=3 by ex2_intro/
]
qed-.

lemma at_inv_xxp: ∀f,i1,i2. @⦃i1, f⦄ ≘ i2 → 0 = i2 →
                  ∃∃g. 0 = i1 & ⫯g = f.
#f elim (pn_split f) *
#g #H #i1 #i2 #Hf #H2
[ /3 width=6 by at_inv_xpp, ex2_intro/
| elim (at_inv_xnp … Hf … H H2)
]
qed-.

lemma at_inv_xxn: ∀f,i1,i2. @⦃i1, f⦄ ≘ i2 → ∀j2.  ↑j2 = i2 →
                  (∃∃g,j1. @⦃j1, g⦄ ≘ j2 & ↑j1 = i1 & ⫯g = f) ∨
                  ∃∃g. @⦃i1, g⦄ ≘ j2 & ↑g = f.
#f elim (pn_split f) *
#g #H #i1 #i2 #Hf #j2 #H2
[ elim (at_inv_xpn … Hf … H H2) -i2 /3 width=5 by or_introl, ex3_2_intro/
| lapply (at_inv_xnn … Hf … H H2) -i2 /3 width=3 by or_intror, ex2_intro/
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma at_increasing: ∀i2,i1,f. @⦃i1, f⦄ ≘ i2 → i1 ≤ i2.
#i2 elim i2 -i2
[ #i1 #f #Hf elim (at_inv_xxp … Hf) -Hf //
| #i2 #IH * //
  #i1 #f #Hf elim (at_inv_nxn … Hf) -Hf [1,4: * |*: // ]
  /3 width=2 by le_S_S, le_S/
]
qed-.

lemma at_increasing_strict: ∀g,i1,i2. @⦃i1, g⦄ ≘ i2 → ∀f. ↑f = g →
                            i1 < i2 ∧ @⦃i1, f⦄ ≘ ↓i2.
#g #i1 #i2 #Hg #f #H elim (at_inv_xnx … Hg … H) -Hg -H
/4 width=2 by conj, at_increasing, le_S_S/
qed-.

lemma at_fwd_id_ex: ∀f,i. @⦃i, f⦄ ≘ i → ∃g. ⫯g = f.
#f elim (pn_split f) * /2 width=2 by ex_intro/
#g #H #i #Hf elim (at_inv_xnx … Hf … H) -Hf -H
#j2 #Hg #H destruct lapply (at_increasing … Hg) -Hg
#H elim (lt_le_false … H) -H //
qed-.

(* Basic properties *********************************************************)

corec lemma at_eq_repl_back: ∀i1,i2. eq_repl_back (λf. @⦃i1, f⦄ ≘ i2).
#i1 #i2 #f1 #H1 cases H1 -f1 -i1 -i2
[ #f1 #g1 #j1 #j2 #H #H1 #H2 #f2 #H12 cases (eq_inv_px … H12 … H) -g1 /2 width=2 by at_refl/
| #f1 #i1 #i2 #Hf1 #g1 #j1 #j2 #H #H1 #H2 #f2 #H12 cases (eq_inv_px … H12 … H) -g1 /3 width=7 by at_push/
| #f1 #i1 #i2 #Hf1 #g1 #j2 #H #H2 #f2 #H12 cases (eq_inv_nx … H12 … H) -g1 /3 width=5 by at_next/
]
qed-.

lemma at_eq_repl_fwd: ∀i1,i2. eq_repl_fwd (λf. @⦃i1, f⦄ ≘ i2).
#i1 #i2 @eq_repl_sym /2 width=3 by at_eq_repl_back/
qed-.

lemma at_le_ex: ∀j2,i2,f. @⦃i2, f⦄ ≘ j2 → ∀i1. i1 ≤ i2 →
                ∃∃j1. @⦃i1, f⦄ ≘ j1 & j1 ≤ j2.
#j2 elim j2 -j2 [2: #j2 #IH ] #i2 #f #Hf
[ elim (at_inv_xxn … Hf) -Hf [1,3: * |*: // ]
  #g [ #x2 ] #Hg [ #H2 ] #H0
  [ * /3 width=3 by at_refl, ex2_intro/
    #i1 #Hi12 destruct lapply (le_S_S_to_le … Hi12) -Hi12
    #Hi12 elim (IH … Hg … Hi12) -x2 -IH
    /3 width=7 by at_push, ex2_intro, le_S_S/
  | #i1 #Hi12 elim (IH … Hg … Hi12) -IH -i2
    /3 width=5 by at_next, ex2_intro, le_S_S/
  ]
| elim (at_inv_xxp … Hf) -Hf //
  #g * -i2 #H2 #i1 #Hi12 <(le_n_O_to_eq … Hi12)
  /3 width=3 by at_refl, ex2_intro/
]
qed-.

lemma at_id_le: ∀i1,i2. i1 ≤ i2 → ∀f. @⦃i2, f⦄ ≘ i2 → @⦃i1, f⦄ ≘ i1.
#i1 #i2 #H @(le_elim … H) -i1 -i2 [ #i2 | #i1 #i2 #IH ]
#f #Hf elim (at_fwd_id_ex … Hf) /4 width=7 by at_inv_npn, at_push, at_refl/
qed-.

(* Main properties **********************************************************)

theorem at_monotonic: ∀j2,i2,f. @⦃i2, f⦄ ≘ j2 → ∀j1,i1. @⦃i1, f⦄ ≘ j1 →
                      i1 < i2 → j1 < j2.
#j2 elim j2 -j2
[ #i2 #f #H2f elim (at_inv_xxp … H2f) -H2f //
  #g #H21 #_ #j1 #i1 #_ #Hi elim (lt_le_false … Hi) -Hi //
| #j2 #IH #i2 #f #H2f * //
  #j1 #i1 #H1f #Hi elim (lt_inv_gen … Hi)
  #x2 #_ #H21 elim (at_inv_nxn … H2f … H21) -H2f [1,3: * |*: // ]
  #g #H2g #H
  [ elim (at_inv_xpn … H1f … H) -f
    /4 width=8 by lt_S_S_to_lt, lt_S_S/
  | /4 width=8 by at_inv_xnn, lt_S_S/
  ]
]
qed-.

theorem at_inv_monotonic: ∀j1,i1,f. @⦃i1, f⦄ ≘ j1 → ∀j2,i2. @⦃i2, f⦄ ≘ j2 →
                          j1 < j2 → i1 < i2.
#j1 elim j1 -j1
[ #i1 #f #H1f elim (at_inv_xxp … H1f) -H1f //
  #g * -i1 #H #j2 #i2 #H2f #Hj elim (lt_inv_O1 … Hj) -Hj
  #x2 #H22 elim (at_inv_xpn … H2f … H H22) -f //
| #j1 #IH *
  [ #f #H1f elim (at_inv_pxn … H1f) -H1f [ |*: // ]
    #g #H1g #H #j2 #i2 #H2f #Hj elim (lt_inv_S1 … Hj) -Hj
    /3 width=7 by at_inv_xnn/
  | #i1 #f #H1f #j2 #i2 #H2f #Hj elim (lt_inv_S1 … Hj) -Hj
    #y2 #Hj #H22 elim (at_inv_nxn … H1f) -H1f [1,4: * |*: // ]
    #g #Hg #H
    [ elim (at_inv_xpn … H2f … H H22) -f -H22
      /3 width=7 by lt_S_S/
    | /3 width=7 by at_inv_xnn/
    ]
  ]
]
qed-.

theorem at_mono: ∀f,i,i1. @⦃i, f⦄ ≘ i1 → ∀i2. @⦃i, f⦄ ≘ i2 → i2 = i1.
#f #i #i1 #H1 #i2 #H2 elim (lt_or_eq_or_gt i2 i1) //
#Hi elim (lt_le_false i i) /3 width=6 by at_inv_monotonic, eq_sym/
qed-.

theorem at_inj: ∀f,i1,i. @⦃i1, f⦄ ≘ i → ∀i2. @⦃i2, f⦄ ≘ i → i1 = i2.
#f #i1 #i #H1 #i2 #H2 elim (lt_or_eq_or_gt i2 i1) //
#Hi elim (lt_le_false i i) /3 width=6 by at_monotonic, eq_sym/
qed-.

theorem at_div_comm: ∀f2,g2,f1,g1.
                     H_at_div f2 g2 f1 g1 → H_at_div g2 f2 g1 f1.
#f2 #g2 #f1 #g1 #IH #jg #jf #j #Hg #Hf
elim (IH … Hf Hg) -IH -j /2 width=3 by ex2_intro/
qed-.

theorem at_div_pp: ∀f2,g2,f1,g1.
                   H_at_div f2 g2 f1 g1 → H_at_div (⫯f2) (⫯g2) (⫯f1) (⫯g1).
#f2 #g2 #f1 #g1 #IH #jf #jg #j #Hf #Hg
elim (at_inv_xpx … Hf) -Hf [1,2: * |*: // ]
[ #H1 #H2 destruct -IH
  lapply (at_inv_xpp … Hg ???) -Hg [4: |*: // ] #H destruct
  /3 width=3 by at_refl, ex2_intro/
| #xf #i #Hf2 #H1 #H2 destruct
  lapply (at_inv_xpn … Hg ????) -Hg [5: * |*: // ] #xg #Hg2 #H destruct
  elim (IH … Hf2 Hg2) -IH -i /3 width=9 by at_push, ex2_intro/
]
qed-.

theorem at_div_nn: ∀f2,g2,f1,g1.
                   H_at_div f2 g2 f1 g1 → H_at_div (↑f2) (↑g2) (f1) (g1).
#f2 #g2 #f1 #g1 #IH #jf #jg #j #Hf #Hg
elim (at_inv_xnx … Hf) -Hf [ |*: // ] #i #Hf2 #H destruct
lapply (at_inv_xnn … Hg ????) -Hg [5: |*: // ] #Hg2
elim (IH … Hf2 Hg2) -IH -i /2 width=3 by ex2_intro/
qed-.

theorem at_div_np: ∀f2,g2,f1,g1.
                   H_at_div f2 g2 f1 g1 → H_at_div (↑f2) (⫯g2) (f1) (↑g1).
#f2 #g2 #f1 #g1 #IH #jf #jg #j #Hf #Hg
elim (at_inv_xnx … Hf) -Hf [ |*: // ] #i #Hf2 #H destruct
lapply (at_inv_xpn … Hg ????) -Hg [5: * |*: // ] #xg #Hg2 #H destruct
elim (IH … Hf2 Hg2) -IH -i /3 width=7 by at_next, ex2_intro/
qed-.

theorem at_div_pn: ∀f2,g2,f1,g1.
                   H_at_div f2 g2 f1 g1 → H_at_div (⫯f2) (↑g2) (↑f1) (g1).
/4 width=6 by at_div_np, at_div_comm/ qed-.

(* Properties on tls ********************************************************)

lemma at_pxx_tls: ∀n,f. @⦃0, f⦄ ≘ n → @⦃0, ⫱*[n]f⦄ ≘ 0.
#n elim n -n //
#n #IH #f #Hf
cases (at_inv_pxn … Hf) -Hf [ |*: // ] #g #Hg #H0 destruct
<tls_xn /2 width=1 by/
qed.

lemma at_tls: ∀i2,f. ⫯⫱*[↑i2]f ≡ ⫱*[i2]f → ∃i1. @⦃i1, f⦄ ≘ i2.
#i2 elim i2 -i2
[ /4 width=4 by at_eq_repl_back, at_refl, ex_intro/
| #i2 #IH #f <tls_xn <tls_xn in ⊢ (??%→?); #H
  elim (IH … H) -IH -H #i1 #Hf
  elim (pn_split f) * #g #Hg destruct /3 width=8 by at_push, at_next, ex_intro/  
]
qed-.

(* Inversion lemmas with tls ************************************************)

lemma at_inv_nxx: ∀n,g,i1,j2. @⦃↑i1, g⦄ ≘ j2 → @⦃0, g⦄ ≘ n →
                  ∃∃i2. @⦃i1, ⫱*[↑n]g⦄ ≘ i2 & ↑(n+i2) = j2.
#n elim n -n
[ #g #i1 #j2 #Hg #H
  elim (at_inv_pxp … H) -H [ |*: // ] #f #H0
  elim (at_inv_npx … Hg … H0) -Hg [ |*: // ] #x2 #Hf #H2 destruct
  /2 width=3 by ex2_intro/
| #n #IH #g #i1 #j2 #Hg #H
  elim (at_inv_pxn … H) -H [ |*: // ] #f #Hf2 #H0
  elim (at_inv_xnx … Hg … H0) -Hg #x2 #Hf1 #H2 destruct
  elim (IH … Hf1 Hf2) -IH -Hf1 -Hf2 #i2 #Hf #H2 destruct
  /2 width=3 by ex2_intro/
]
qed-.

lemma at_inv_tls: ∀i2,i1,f. @⦃i1, f⦄ ≘ i2 → ⫯⫱*[↑i2]f ≡ ⫱*[i2]f.
#i2 elim i2 -i2
[ #i1 #f #Hf elim (at_inv_xxp … Hf) -Hf // #g #H1 #H destruct
  /2 width=1 by eq_refl/
| #i2 #IH #i1 #f #Hf
  elim (at_inv_xxn … Hf) -Hf [1,3: * |*: // ]
  [ #g #j1 #Hg #H1 #H2 | #g #Hg #Ho ] destruct
  <tls_xn /2 width=2 by/
]
qed-.

(* Advanced inversion lemmas on isid ****************************************)

lemma isid_inv_at: ∀i,f. 𝐈⦃f⦄ → @⦃i, f⦄ ≘ i.
#i elim i -i
[ #f #H elim (isid_inv_gen … H) -H /2 width=2 by at_refl/
| #i #IH #f #H elim (isid_inv_gen … H) -H /3 width=7 by at_push/
]
qed.

lemma isid_inv_at_mono: ∀f,i1,i2. 𝐈⦃f⦄ → @⦃i1, f⦄ ≘ i2 → i1 = i2.
/3 width=6 by isid_inv_at, at_mono/ qed-.

(* Advanced properties on isid **********************************************)

corec lemma isid_at: ∀f. (∀i. @⦃i, f⦄ ≘ i) → 𝐈⦃f⦄.
#f #Hf lapply (Hf 0)
#H cases (at_fwd_id_ex … H) -H
#g #H @(isid_push … H) /3 width=7 by at_inv_npn/
qed-.

(* Advanced properties on id ************************************************)

lemma id_inv_at: ∀f. (∀i. @⦃i, f⦄ ≘ i) → 𝐈𝐝 ≡ f.
/3 width=1 by isid_at, eq_id_inv_isid/ qed-.

lemma id_at: ∀i. @⦃i, 𝐈𝐝⦄ ≘ i.
/2 width=1 by isid_inv_at/ qed.

(* Advanced forward lemmas on id ********************************************)

lemma at_id_fwd: ∀i1,i2. @⦃i1, 𝐈𝐝⦄ ≘ i2 → i1 = i2.
/2 width=4 by at_mono/ qed.

(* Main properties on id ****************************************************)

theorem at_div_id_dx: ∀f. H_at_div f 𝐈𝐝 𝐈𝐝 f.
#f #jf #j0 #j #Hf #H0
lapply (at_id_fwd … H0) -H0 #H destruct
/2 width=3 by ex2_intro/
qed-.

theorem at_div_id_sn: ∀f. H_at_div 𝐈𝐝 f f 𝐈𝐝.
/3 width=6 by at_div_id_dx, at_div_comm/ qed-.

(* Properties with uniform relocations **************************************)

lemma at_uni: ∀n,i. @⦃i,𝐔❴n❵⦄ ≘ n+i.
#n elim n -n /2 width=5 by at_next/
qed.

(* Inversion lemmas with uniform relocations ********************************)

lemma at_inv_uni: ∀n,i,j. @⦃i,𝐔❴n❵⦄ ≘ j → j = n+i.
/2 width=4 by at_mono/ qed-.
