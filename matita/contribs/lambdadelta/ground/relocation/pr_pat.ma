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

include "ground/notation/relations/ratsharp_3.ma".
include "ground/xoa/ex_3_2.ma".
include "ground/arith/pnat.ma".
include "ground/relocation/pr_tl.ma".

(* POSITIVE APPLICATION FOR PARTIAL RELOCATION MAPS *************************)

(*** at *)
coinductive pr_pat: relation3 pr_map pnat pnat ≝
(*** at_refl *)
| pr_pat_refl (f) (g) (j1) (j2):
  ⫯f = g → 𝟏 = j1 → 𝟏 = j2 → pr_pat g j1 j2
(*** at_push *)
| pr_pat_push (f) (i1) (i2):
  pr_pat f i1 i2 → ∀g,j1,j2. ⫯f = g → ↑i1 = j1 → ↑i2 = j2 → pr_pat g j1 j2
(*** at_next *)
| pr_pat_next (f) (i1) (i2):
  pr_pat f i1 i2 → ∀g,j2. ↑f = g → ↑i2 = j2 → pr_pat g i1 j2
.

interpretation
  "relational positive application (partial relocation maps)"
  'RAtSharp i1 f i2 = (pr_pat f i1 i2).

(*** H_at_div *)
definition H_pr_pat_div: relation4 pr_map pr_map pr_map pr_map ≝
           λf2,g2,f1,g1.
           ∀jf,jg,j. ＠⧣❨jf,f2❩ ≘ j → ＠⧣❨jg,g2❩ ≘ j →
           ∃∃j0. ＠⧣❨j0,f1❩ ≘ jf & ＠⧣❨j0,g1❩ ≘ jg.

(* Basic inversions *********************************************************)

(*** at_inv_ppx *)
lemma pr_pat_inv_unit_push (f) (i1) (i2):
      ＠⧣❨i1,f❩ ≘ i2 → ∀g. 𝟏 = i1 → ⫯g = f → 𝟏 = i2.
#f #i1 #i2 * -f -i1 -i2 //
[ #f #i1 #i2 #_ #g #j1 #j2 #_ * #_ #x #H destruct
| #f #i1 #i2 #_ #g #j2 * #_ #x #_ #H elim (eq_inv_pr_push_next … H)
]
qed-.

(*** at_inv_npx *)
lemma pr_pat_inv_succ_push (f) (i1) (i2):
      ＠⧣❨i1,f❩ ≘ i2 → ∀g,j1. ↑j1 = i1 → ⫯g = f →
      ∃∃j2. ＠⧣❨j1,g❩ ≘ j2 & ↑j2 = i2.
#f #i1 #i2 * -f -i1 -i2
[ #f #g #j1 #j2 #_ * #_ #x #x1 #H destruct
| #f #i1 #i2 #Hi #g #j1 #j2 * * * #x #x1 #H #Hf >(eq_inv_pr_push_bi … Hf) -g destruct /2 width=3 by ex2_intro/
| #f #i1 #i2 #_ #g #j2 * #_ #x #x1 #_ #H elim (eq_inv_pr_push_next … H)
]
qed-.

(*** at_inv_xnx *)
lemma pr_pat_inv_next (f) (i1) (i2):
      ＠⧣❨i1,f❩ ≘ i2 → ∀g. ↑g = f →
      ∃∃j2. ＠⧣❨i1,g❩ ≘ j2 & ↑j2 = i2.
#f #i1 #i2 * -f -i1 -i2
[ #f #g #j1 #j2 * #_ #_ #x #H elim (eq_inv_pr_next_push … H)
| #f #i1 #i2 #_ #g #j1 #j2 * #_ #_ #x #H elim (eq_inv_pr_next_push … H)
| #f #i1 #i2 #Hi #g #j2 * * #x #H >(eq_inv_pr_next_bi … H) -g /2 width=3 by ex2_intro/
]
qed-.

(* Advanced inversions ******************************************************)

(*** at_inv_ppn *)
lemma pr_pat_inv_unit_push_succ (f) (i1) (i2):
      ＠⧣❨i1,f❩ ≘ i2 → ∀g,j2. 𝟏 = i1 → ⫯g = f → ↑j2 = i2 → ⊥.
#f #i1 #i2 #Hf #g #j2 #H1 #H <(pr_pat_inv_unit_push … Hf … H1 H) -f -g -i1 -i2
#H destruct
qed-.

(*** at_inv_npp *)
lemma pr_pat_inv_succ_push_unit (f) (i1) (i2):
      ＠⧣❨i1,f❩ ≘ i2 → ∀g,j1. ↑j1 = i1 → ⫯g = f → 𝟏 = i2 → ⊥.
#f #i1 #i2 #Hf #g #j1 #H1 #H elim (pr_pat_inv_succ_push … Hf … H1 H) -f -i1
#x2 #Hg * -i2 #H destruct
qed-.

(*** at_inv_npn *)
lemma pr_pat_inv_succ_push_succ (f) (i1) (i2):
      ＠⧣❨i1,f❩ ≘ i2 → ∀g,j1,j2. ↑j1 = i1 → ⫯g = f → ↑j2 = i2 → ＠⧣❨j1,g❩ ≘ j2.
#f #i1 #i2 #Hf #g #j1 #j2 #H1 #H elim (pr_pat_inv_succ_push … Hf … H1 H) -f -i1
#x2 #Hg * -i2 #H destruct //
qed-.

(*** at_inv_xnp *)
lemma pr_pat_inv_next_unit (f) (i1) (i2):
      ＠⧣❨i1,f❩ ≘ i2 → ∀g. ↑g = f → 𝟏 = i2 → ⊥.
#f #i1 #i2 #Hf #g #H elim (pr_pat_inv_next … Hf … H) -f
#x2 #Hg * -i2 #H destruct
qed-.

(*** at_inv_xnn *)
lemma pr_pat_inv_next_succ (f) (i1) (i2):
      ＠⧣❨i1,f❩ ≘ i2 → ∀g,j2. ↑g = f → ↑j2 = i2 → ＠⧣❨i1,g❩ ≘ j2.
#f #i1 #i2 #Hf #g #j2 #H elim (pr_pat_inv_next … Hf … H) -f
#x2 #Hg * -i2 #H destruct //
qed-.

(*** at_inv_pxp *)
lemma pr_pat_inv_unit_bi (f) (i1) (i2):
      ＠⧣❨i1,f❩ ≘ i2 → 𝟏 = i1 → 𝟏 = i2 → ∃g. ⫯g = f.
#f elim (pr_map_split_tl … f) /2 width=2 by ex_intro/
#H #i1 #i2 #Hf #H1 #H2 cases (pr_pat_inv_next_unit … Hf … H H2)
qed-.

(*** at_inv_pxn *)
lemma pr_pat_inv_unit_succ (f) (i1) (i2):
      ＠⧣❨i1,f❩ ≘ i2 → ∀j2. 𝟏 = i1 → ↑j2 = i2 →
      ∃∃g. ＠⧣❨i1,g❩ ≘ j2 & ↑g = f.
#f elim (pr_map_split_tl … f)
#H #i1 #i2 #Hf #j2 #H1 #H2
[ elim (pr_pat_inv_unit_push_succ … Hf … H1 H H2)
| /3 width=5 by pr_pat_inv_next_succ, ex2_intro/
]
qed-.

(*** at_inv_nxp *)
lemma pr_pat_inv_succ_unit (f) (i1) (i2):
      ＠⧣❨i1,f❩ ≘ i2 → ∀j1. ↑j1 = i1 → 𝟏 = i2 → ⊥.
#f elim (pr_map_split_tl f)
#H #i1 #i2 #Hf #j1 #H1 #H2
[ elim (pr_pat_inv_succ_push_unit … Hf … H1 H H2)
| elim (pr_pat_inv_next_unit … Hf … H H2)
]
qed-.

(*** at_inv_nxn *)
lemma pr_pat_inv_succ_bi (f) (i1) (i2):
      ＠⧣❨i1,f❩ ≘ i2 → ∀j1,j2. ↑j1 = i1 → ↑j2 = i2 →
      ∨∨ ∃∃g. ＠⧣❨j1,g❩ ≘ j2 & ⫯g = f
       | ∃∃g. ＠⧣❨i1,g❩ ≘ j2 & ↑g = f.
#f elim (pr_map_split_tl f) *
/4 width=7 by pr_pat_inv_next_succ, pr_pat_inv_succ_push_succ, ex2_intro, or_intror, or_introl/
qed-.

(* Note: the following inversion lemmas must be checked *)
(*** at_inv_xpx *)
lemma pr_pat_inv_push (f) (i1) (i2):
      ＠⧣❨i1,f❩ ≘ i2 → ∀g. ⫯g = f →
      ∨∨ ∧∧ 𝟏 = i1 & 𝟏 = i2
       | ∃∃j1,j2. ＠⧣❨j1,g❩ ≘ j2 & ↑j1 = i1 & ↑j2 = i2.
#f * [2: #i1 ] #i2 #Hf #g #H
[ elim (pr_pat_inv_succ_push … Hf … H) -f /3 width=5 by or_intror, ex3_2_intro/
| >(pr_pat_inv_unit_push … Hf … H) -f /3 width=1 by conj, or_introl/
]
qed-.

(*** at_inv_xpp *)
lemma pr_pat_inv_push_unit (f) (i1) (i2):
      ＠⧣❨i1,f❩ ≘ i2 → ∀g. ⫯g = f → 𝟏 = i2 → 𝟏 = i1.
#f #i1 #i2 #Hf #g #H elim (pr_pat_inv_push … Hf … H) -f * //
#j1 #j2 #_ #_ * -i2 #H destruct
qed-.

(*** at_inv_xpn *)
lemma pr_pat_inv_push_succ (f) (i1) (i2):
      ＠⧣❨i1,f❩ ≘ i2 → ∀g,j2. ⫯g = f → ↑j2 = i2 →
      ∃∃j1. ＠⧣❨j1,g❩ ≘ j2 & ↑j1 = i1.
#f #i1 #i2 #Hf #g #j2 #H elim (pr_pat_inv_push … Hf … H) -f *
[ #_ * -i2 #H destruct
| #x1 #x2 #Hg #H1 * -i2 #H destruct /2 width=3 by ex2_intro/
]
qed-.

(*** at_inv_xxp *)
lemma pr_pat_inv_unit_dx (f) (i1) (i2):
      ＠⧣❨i1,f❩ ≘ i2 → 𝟏 = i2 →
      ∃∃g. 𝟏 = i1 & ⫯g = f.
#f elim (pr_map_split_tl f)
#H #i1 #i2 #Hf #H2
[ /3 width=6 by pr_pat_inv_push_unit, ex2_intro/
| elim (pr_pat_inv_next_unit … Hf … H H2)
]
qed-.

(*** at_inv_xxn *)
lemma pr_pat_inv_succ_dx (f) (i1) (i2):
      ＠⧣❨i1,f❩ ≘ i2 → ∀j2.  ↑j2 = i2 →
      ∨∨ ∃∃g,j1. ＠⧣❨j1,g❩ ≘ j2 & ↑j1 = i1 & ⫯g = f
       | ∃∃g. ＠⧣❨i1,g❩ ≘ j2 & ↑g = f.
#f elim (pr_map_split_tl f)
#H #i1 #i2 #Hf #j2 #H2
[ elim (pr_pat_inv_push_succ … Hf … H H2) -i2 /3 width=5 by or_introl, ex3_2_intro/
| lapply (pr_pat_inv_next_succ … Hf … H H2) -i2 /3 width=3 by or_intror, ex2_intro/
]
qed-.
