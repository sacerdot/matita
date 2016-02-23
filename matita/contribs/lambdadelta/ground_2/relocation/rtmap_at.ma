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
include "ground_2/relocation/rtmap_id.ma".

(* RELOCATION MAP ***********************************************************)

coinductive at: rtmap → relation nat ≝
| at_refl: ∀f,g,j1,j2. ↑f = g → 0 = j1 → 0 = j2 → at g j1 j2 
| at_push: ∀f,i1,i2. at f i1 i2 → ∀g,j1,j2. ↑f = g → ⫯i1 = j1 → ⫯i2 = j2 → at g j1 j2
| at_next: ∀f,i1,i2. at f i1 i2 → ∀g,j2. ⫯f = g → ⫯i2 = j2 → at g i1 j2
.

interpretation "relational application (rtmap)"
   'RAt i1 f i2 = (at f i1 i2).

(* Basic inversion lemmas ***************************************************)

lemma at_inv_ppx: ∀f,i1,i2. @⦃i1, f⦄ ≡ i2 → ∀g. 0 = i1 → ↑g = f → 0 = i2.
#f #i1 #i2 * -f -i1 -i2 //
[ #f #i1 #i2 #_ #g #j1 #j2 #_ * #_ #x #H destruct
| #f #i1 #i2 #_ #g #j2 * #_ #x #_ #H elim (discr_push_next … H)
]
qed-.

lemma at_inv_npx: ∀f,i1,i2. @⦃i1, f⦄ ≡ i2 → ∀g,j1. ⫯j1 = i1 → ↑g = f →
                  ∃∃j2. @⦃j1, g⦄ ≡ j2 & ⫯j2 = i2.
#f #i1 #i2 * -f -i1 -i2
[ #f #g #j1 #j2 #_ * #_ #x #x1 #H destruct
| #f #i1 #i2 #Hi #g #j1 #j2 * * * #x #x1 #H #Hf >(injective_push … Hf) -g destruct /2 width=3 by ex2_intro/
| #f #i1 #i2 #_ #g #j2 * #_ #x #x1 #_ #H elim (discr_push_next … H)
]
qed-.

lemma at_inv_xnx: ∀f,i1,i2. @⦃i1, f⦄ ≡ i2 → ∀g. ⫯g = f →
                  ∃∃j2. @⦃i1, g⦄ ≡ j2 & ⫯j2 = i2.
#f #i1 #i2 * -f -i1 -i2
[ #f #g #j1 #j2 * #_ #_ #x #H elim (discr_next_push … H)
| #f #i1 #i2 #_ #g #j1 #j2 * #_ #_ #x #H elim (discr_next_push … H)
| #f #i1 #i2 #Hi #g #j2 * * #x #H >(injective_next … H) -g /2 width=3 by ex2_intro/
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma at_inv_ppn: ∀f,i1,i2. @⦃i1, f⦄ ≡ i2 →
                  ∀g,j2. 0 = i1 → ↑g = f → ⫯j2 = i2 → ⊥.
#f #i1 #i2 #Hf #g #j2 #H1 #H <(at_inv_ppx … Hf … H1 H) -f -g -i1 -i2
#H destruct
qed-.

lemma at_inv_npn: ∀f,i1,i2. @⦃i1, f⦄ ≡ i2 →
                  ∀g,j1,j2. ⫯j1 = i1 → ↑g = f → ⫯j2 = i2 → @⦃j1, g⦄ ≡ j2.
#f #i1 #i2 #Hf #g #j1 #j2 #H1 #H elim (at_inv_npx … Hf … H1 H) -f -i1
#x2 #Hg * -i2 #H destruct //
qed-.

lemma at_inv_npp: ∀f,i1,i2. @⦃i1, f⦄ ≡ i2 →
                  ∀g,j1. ⫯j1 = i1 → ↑g = f → 0 = i2 → ⊥.
#f #i1 #i2 #Hf #g #j1 #H1 #H elim (at_inv_npx … Hf … H1 H) -f -i1
#x2 #Hg * -i2 #H destruct
qed-.

lemma at_inv_xnn: ∀f,i1,i2. @⦃i1, f⦄ ≡ i2 →
                  ∀g,j2. ⫯g = f → ⫯j2 = i2 → @⦃i1, g⦄ ≡ j2.
#f #i1 #i2 #Hf #g #j2 #H elim (at_inv_xnx … Hf … H) -f
#x2 #Hg * -i2 #H destruct //
qed-.

lemma at_inv_pxn: ∀f,i1,i2. @⦃i1, f⦄ ≡ i2 → ∀j2. 0 = i1 → ⫯j2 = i2 →
                  ∃∃g. @⦃i1, g⦄ ≡ j2 & ⫯g = f.
#f elim (pn_split … f) *
#g #H #i1 #i2 #Hf #j2 #H1 #H2
[ elim (at_inv_ppn … Hf … H1 H H2)
| /3 width=5 by at_inv_xnn, ex2_intro/
]
qed-.

lemma at_inv_xnp: ∀f,i1,i2. @⦃i1, f⦄ ≡ i2 →
                  ∀g. ⫯g = f → 0 = i2 → ⊥.
#f #i1 #i2 #Hf #g #H elim (at_inv_xnx … Hf … H) -f
#x2 #Hg * -i2 #H destruct
qed-.

lemma at_inv_nxp: ∀f,i1,i2. @⦃i1, f⦄ ≡ i2 →
                  ∀j1. ⫯j1 = i1 → 0 = i2 → ⊥.
#f elim (pn_split f) *
#g #H #i1 #i2 #Hf #j1 #H1 #H2
[ elim (at_inv_npp … Hf … H1 H H2)
| elim (at_inv_xnp … Hf … H H2)
]
qed-.

lemma at_inv_nxn: ∀f,i1,i2. @⦃i1, f⦄ ≡ i2 → ∀j1,j2. ⫯j1 = i1 → ⫯j2 = i2 →
                  (∃∃g. @⦃j1, g⦄ ≡ j2 & ↑g = f) ∨
                  ∃∃g. @⦃i1, g⦄ ≡ j2 & ⫯g = f.
#f elim (pn_split f) *
/4 width=7 by at_inv_xnn, at_inv_npn, ex2_intro, or_intror, or_introl/
qed-.

lemma at_inv_xpx: ∀f,i1,i2. @⦃i1, f⦄ ≡ i2 → ∀g. ↑g = f →
                  (0 = i1 ∧ 0 = i2) ∨
                  ∃∃j1,j2. @⦃j1, g⦄ ≡ j2 & ⫯j1 = i1 & ⫯j2 = i2.
#f * [2: #i1 ] #i2 #Hf #g #H
[ elim (at_inv_npx … Hf … H) -f /3 width=5 by or_intror, ex3_2_intro/
| >(at_inv_ppx … Hf … H) -f /3 width=1 by conj, or_introl/
]
qed-.

lemma at_inv_xpp: ∀f,i1,i2. @⦃i1, f⦄ ≡ i2 → ∀g. ↑g = f → 0 = i2 → 0 = i1.
#f #i1 #i2 #Hf #g #H elim (at_inv_xpx … Hf … H) -f * //
#j1 #j2 #_ #_ * -i2 #H destruct
qed-.

lemma at_inv_xpn: ∀f,i1,i2. @⦃i1, f⦄ ≡ i2 → ∀g,j2. ↑g = f → ⫯j2 = i2 →
                  ∃∃j1. @⦃j1, g⦄ ≡ j2 & ⫯j1 = i1.
#f #i1 #i2 #Hf #g #j2 #H elim (at_inv_xpx … Hf … H) -f *
[ #_ * -i2 #H destruct
| #x1 #x2 #Hg #H1 * -i2 #H destruct /2 width=3 by ex2_intro/
]
qed-.

lemma at_inv_xxp: ∀f,i1,i2. @⦃i1, f⦄ ≡ i2 → 0 = i2 →
                  ∃∃g. 0 = i1 & ↑g = f.
#f elim (pn_split f) *
#g #H #i1 #i2 #Hf #H2
[ /3 width=6 by at_inv_xpp, ex2_intro/
| elim (at_inv_xnp … Hf … H H2)
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma at_increasing: ∀i2,i1,f. @⦃i1, f⦄ ≡ i2 → i1 ≤ i2.
#i2 elim i2 -i2
[ #i1 #f #Hf elim (at_inv_xxp … Hf) -Hf //
| #i2 #IH * //
  #i1 #f #Hf elim (at_inv_nxn … Hf) -Hf [1,4: * |*: // ]
  /3 width=2 by le_S_S, le_S/
]
qed-.

lemma at_increasing_strict: ∀g,i1,i2. @⦃i1, g⦄ ≡ i2 → ∀f. ⫯f = g →
                            i1 < i2 ∧ @⦃i1, f⦄ ≡ ⫰i2.
#g #i1 #i2 #Hg #f #H elim (at_inv_xnx … Hg … H) -Hg -H
/4 width=2 by conj, at_increasing, le_S_S/
qed-.

lemma at_fwd_id_ex: ∀f,i. @⦃i, f⦄ ≡ i → ∃g. ↑g = f.
#f elim (pn_split f) * /2 width=2 by ex_intro/
#g #H #i #Hf elim (at_inv_xnx … Hf … H) -Hf -H
#j2 #Hg #H destruct lapply (at_increasing … Hg) -Hg
#H elim (lt_le_false … H) -H //
qed-.

(* Basic properties *********************************************************)

let corec at_eq_repl_back: ∀i1,i2. eq_repl_back (λf. @⦃i1, f⦄ ≡ i2) ≝ ?.
#i1 #i2 #f1 #H1 cases H1 -f1 -i1 -i2
[ #f1 #g1 #j1 #j2 #H #H1 #H2 #f2 #H12 cases (eq_inv_px … H12 … H) -g1 /2 width=2 by at_refl/
| #f1 #i1 #i2 #Hf1 #g1 #j1 #j2 #H #H1 #H2 #f2 #H12 cases (eq_inv_px … H12 … H) -g1 /3 width=7 by at_push/
| #f1 #i1 #i2 #Hf1 #g1 #j2 #H #H2 #f2 #H12 cases (eq_inv_nx … H12 … H) -g1 /3 width=5 by at_next/
]
qed-.

lemma at_eq_repl_fwd: ∀i1,i2. eq_repl_fwd (λf. @⦃i1, f⦄ ≡ i2).
#i1 #i2 @eq_repl_sym /2 width=3 by at_eq_repl_back/
qed-.

lemma at_id_le: ∀i1,i2. i1 ≤ i2 → ∀f. @⦃i2, f⦄ ≡ i2 → @⦃i1, f⦄ ≡ i1.
#i1 #i2 #H @(le_elim … H) -i1 -i2 [ #i2 | #i1 #i2 #IH ]
#f #Hf elim (at_fwd_id_ex … Hf) /4 width=7 by at_inv_npn, at_push, at_refl/
qed-.

(* Main properties **********************************************************)

theorem at_monotonic: ∀j2,i2,f2. @⦃i2, f2⦄ ≡ j2 → ∀j1,i1,f1. @⦃i1, f1⦄ ≡ j1 →
                      f1 ≗ f2 → i1 < i2 → j1 < j2.
#j2 elim j2 -j2
[ #i2 #f2 #Hf2 elim (at_inv_xxp … Hf2) -Hf2 //
  #g #H21 #_ #j1 #i1 #f1 #_ #_ #Hi elim (lt_le_false … Hi) -Hi //
| #j2 #IH #i2 #f2 #Hf2 * //
  #j1 #i1 #f1 #Hf1 #Hf #Hi elim (lt_inv_gen … Hi)
  #x2 #_ #H21 elim (at_inv_nxn … Hf2 … H21) -Hf2 [1,3: * |*: // ]
  #g2 #Hg2 #H2
  [ elim (eq_inv_xp … Hf … H2) -f2
    #g1 #Hg #H1 elim (at_inv_xpn … Hf1 … H1) -f1
    /4 width=8 by lt_S_S_to_lt, lt_S_S/
  | elim (eq_inv_xn … Hf … H2) -f2
    /4 width=8 by at_inv_xnn, lt_S_S/
  ]
]
qed-.

theorem at_inv_monotonic: ∀j1,i1,f1. @⦃i1, f1⦄ ≡ j1 → ∀j2,i2,f2. @⦃i2, f2⦄ ≡ j2 →
                          f1 ≗ f2 → j1 < j2 → i1 < i2.
#j1 elim j1 -j1
[ #i1 #f1 #Hf1 elim (at_inv_xxp … Hf1) -Hf1 //
  #g1 * -i1 #H1 #j2 #i2 #f2 #Hf2 #Hf #Hj elim (lt_inv_O1 … Hj) -Hj
  #x2 #H22 elim (eq_inv_px … Hf … H1) -f1
  #g2 #Hg #H2 elim (at_inv_xpn … Hf2 … H2 H22) -f2 //
| #j1 #IH *
  [ #f1 #Hf1 elim (at_inv_pxn … Hf1) -Hf1 [ |*: // ]
    #g1 #Hg1 #H1 #j2 #i2 #f2 #Hf2 #Hf #Hj elim (lt_inv_S1 … Hj) -Hj
    elim (eq_inv_nx … Hf … H1) -f1 /3 width=7 by at_inv_xnn/
  | #i1 #f1 #Hf1 #j2 #i2 #f2 #Hf2 #Hf #Hj elim (lt_inv_S1 … Hj) -Hj
    #y2 #Hj #H22 elim (at_inv_nxn … Hf1) -Hf1 [1,4: * |*: // ]
    #g1 #Hg1 #H1
    [ elim (eq_inv_px … Hf … H1) -f1
      #g2 #Hg #H2 elim (at_inv_xpn … Hf2 … H2 H22) -f2 -H22
      /3 width=7 by lt_S_S/
    | elim (eq_inv_nx … Hf … H1) -f1 /3 width=7 by at_inv_xnn/
    ]
  ]
]
qed-.

theorem at_mono: ∀f1,f2. f1 ≗ f2 → ∀i,i1. @⦃i, f1⦄ ≡ i1 → ∀i2. @⦃i, f2⦄ ≡ i2 → i2 = i1.
#f1 #f2 #Ht #i #i1 #H1 #i2 #H2 elim (lt_or_eq_or_gt i2 i1) //
#Hi elim (lt_le_false i i) /3 width=8 by at_inv_monotonic, eq_sym/
qed-.

theorem at_inj: ∀f1,f2. f1 ≗ f2 → ∀i1,i. @⦃i1, f1⦄ ≡ i → ∀i2. @⦃i2, f2⦄ ≡ i → i1 = i2.
#f1 #f2 #Ht #i1 #i #H1 #i2 #H2 elim (lt_or_eq_or_gt i2 i1) //
#Hi elim (lt_le_false i i) /3 width=8 by at_monotonic, eq_sym/
qed-.

(* Advanced inversion lemmas on isid ****************************************)

lemma isid_inv_at: ∀i,f. 𝐈⦃f⦄ → @⦃i, f⦄ ≡ i.
#i elim i -i
[ #f #H elim (isid_inv_gen … H) -H /2 width=2 by at_refl/
| #i #IH #f #H elim (isid_inv_gen … H) -H /3 width=7 by at_push/
]
qed.

lemma isid_inv_at_mono: ∀f,i1,i2. 𝐈⦃f⦄ → @⦃i1, f⦄ ≡ i2 → i1 = i2.
/3 width=6 by isid_inv_at, at_mono/ qed-.

(* Advancedd properties on isid *********************************************)

let corec isid_at: ∀f. (∀i. @⦃i, f⦄ ≡ i) → 𝐈⦃f⦄ ≝ ?.
#f #Hf lapply (Hf 0)
#H cases (at_fwd_id_ex … H) -H
#g #H @(isid_push … H) /3 width=7 by at_inv_npn/
qed-.

(* Advanced properties on id ************************************************)

lemma id_inv_at: ∀f. (∀i. @⦃i, f⦄ ≡ i) → 𝐈𝐝 ≗ f.
/3 width=1 by isid_at, eq_id_inv_isid/ qed-.

lemma id_at: ∀i. @⦃i, 𝐈𝐝⦄ ≡ i.
/2 width=1 by isid_inv_at/ qed.
