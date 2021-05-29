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

include "ground/relocation/gr_tl.ma".

(* INCLUSION FOR GENERIC RELOCATION MAPS ************************************)

(*** sle *)
coinductive gr_sle: relation gr_map ≝
(*** sle_push *)
| gr_sle_push (f1) (f2) (g1) (g2):
  gr_sle f1 f2 → ⫯f1 = g1 → ⫯f2 = g2 → gr_sle g1 g2
(*** sle_next *)
| gr_sle_next (f1) (f2) (g1) (g2):
  gr_sle f1 f2 → ↑f1 = g1 → ↑f2 = g2 → gr_sle g1 g2
(*** sle_weak *)
| gr_sle_weak (f1) (f2) (g1) (g2):
  gr_sle f1 f2 → ⫯f1 = g1 → ↑f2 = g2 → gr_sle g1 g2
.

interpretation
  "inclusion (generic relocation maps)"
  'subseteq f1 f2 = (gr_sle f1 f2).

(* Basic constructions ******************************************************)

(*** sle_refl *)
corec lemma gr_sle_refl:
            reflexive … gr_sle.
#f cases (gr_map_split_tl f) #H
[ @(gr_sle_push … H H) | @(gr_sle_next … H H) ] -H //
qed.

(* Basic inversions *********************************************************)

(*** sle_inv_xp *)
lemma gr_sle_inv_push_dx:
      ∀g1,g2. g1 ⊆ g2 → ∀f2. ⫯f2 = g2 →
      ∃∃f1. f1 ⊆ f2 & ⫯f1 = g1.
#g1 #g2 * -g1 -g2
#f1 #f2 #g1 #g2 #H #H1 #H2 #x2 #Hx2 destruct
[ lapply (eq_inv_gr_push_bi … Hx2) -Hx2 /2 width=3 by ex2_intro/ ]
elim (eq_inv_gr_push_next … Hx2)
qed-.

(*** sle_inv_nx *)
lemma gr_sle_inv_next_sn:
      ∀g1,g2. g1 ⊆ g2 → ∀f1. ↑f1 = g1 →
      ∃∃f2. f1 ⊆ f2 & ↑f2 = g2.
#g1 #g2 * -g1 -g2
#f1 #f2 #g1 #g2 #H #H1 #H2 #x1 #Hx1 destruct
[2: lapply (eq_inv_gr_next_bi … Hx1) -Hx1 /2 width=3 by ex2_intro/ ]
elim (eq_inv_gr_next_push … Hx1)
qed-.

(*** sle_inv_pn *)
lemma gr_sle_inv_push_next:
      ∀g1,g2. g1 ⊆ g2 → ∀f1,f2. ⫯f1 = g1 → ↑f2 = g2 → f1 ⊆ f2.
#g1 #g2 * -g1 -g2
#f1 #f2 #g1 #g2 #H #H1 #H2 #x1 #x2 #Hx1 #Hx2 destruct
[ elim (eq_inv_gr_next_push … Hx2)
| elim (eq_inv_gr_push_next … Hx1)
| lapply (eq_inv_gr_push_bi … Hx1) -Hx1
  lapply (eq_inv_gr_next_bi … Hx2) -Hx2 //
]
qed-.

(* Advanced inversions ******************************************************)

(*** sle_inv_pp *)
lemma gr_sle_inv_push_bi:
      ∀g1,g2. g1 ⊆ g2 → ∀f1,f2. ⫯f1 = g1 → ⫯f2 = g2 → f1 ⊆ f2.
#g1 #g2 #H #f1 #f2 #H1 #H2
elim (gr_sle_inv_push_dx … H … H2) -g2 #x1 #H #Hx1 destruct
lapply (eq_inv_gr_push_bi … Hx1) -Hx1 //
qed-.

(*** sle_inv_nn *)
lemma gr_sle_inv_next_bi:
      ∀g1,g2. g1 ⊆ g2 → ∀f1,f2. ↑f1 = g1 → ↑f2 = g2 → f1 ⊆ f2.
#g1 #g2 #H #f1 #f2 #H1 #H2
elim (gr_sle_inv_next_sn … H … H1) -g1 #x2 #H #Hx2 destruct
lapply (eq_inv_gr_next_bi … Hx2) -Hx2 //
qed-.

(*** sle_inv_px *)
lemma gr_sle_inv_push_sn:
      ∀g1,g2. g1 ⊆ g2 → ∀f1. ⫯f1 = g1 →
      ∨∨ ∃∃f2. f1 ⊆ f2 & ⫯f2 = g2 
       | ∃∃f2. f1 ⊆ f2 & ↑f2 = g2.
#g1 #g2
elim (gr_map_split_tl g2) #H2 #H #f1 #H1
[ lapply (gr_sle_inv_push_bi … H … H1 H2)
| lapply (gr_sle_inv_push_next … H … H1 H2)
] -H -H1
/3 width=3 by ex2_intro, or_introl, or_intror/
qed-.

(*** sle_inv_xn *)
lemma gr_sle_inv_next_dx:
      ∀g1,g2. g1 ⊆ g2 → ∀f2. ↑f2 = g2 →
      ∨∨ ∃∃f1. f1 ⊆ f2 & ⫯f1 = g1
       | ∃∃f1. f1 ⊆ f2 & ↑f1 = g1.
#g1 #g2
elim (gr_map_split_tl g1) #H1 #H #f2 #H2
[ lapply (gr_sle_inv_push_next … H … H1 H2)
| lapply (gr_sle_inv_next_bi … H … H1 H2)
] -H -H2
/3 width=3 by ex2_intro, or_introl, or_intror/
qed-.

(* Constructions with gr_tl *************************************************)

(*** sle_px_tl *)
lemma gr_sle_push_sn_tl:
      ∀g1,g2. g1 ⊆ g2 → ∀f1. ⫯f1 = g1 → f1 ⊆ ⫱g2.
#g1 #g2 #H #f1 #H1
elim (gr_sle_inv_push_sn … H … H1) -H -H1 * //
qed.

(*** sle_xn_tl *)
lemma gr_sle_next_dx_tl:
      ∀g1,g2. g1 ⊆ g2 → ∀f2. ↑f2 = g2 → ⫱g1 ⊆ f2.
#g1 #g2 #H #f2 #H2
elim (gr_sle_inv_next_dx … H … H2) -H -H2 * //
qed.

(*** sle_tl *)
lemma gr_sle_tl:
      ∀f1,f2. f1 ⊆ f2 → ⫱f1 ⊆ ⫱f2.
#f1 elim (gr_map_split_tl f1) #H1 #f2 #H
[ lapply (gr_sle_push_sn_tl … H … H1) -H //
| elim (gr_sle_inv_next_sn … H … H1) -H //
]
qed.

(* Inversions with gr_tl ****************************************************)

(*** sle_inv_tl_sn *)
lemma gr_sle_inv_tl_sn:
      ∀f1,f2. ⫱f1 ⊆ f2 → f1 ⊆ ↑f2.
#f1 elim (gr_map_split_tl f1) #H #f2 #Hf12
/2 width=5 by gr_sle_next, gr_sle_weak/
qed-.

(*** sle_inv_tl_dx *)
lemma gr_sle_inv_tl_dx:
      ∀f1,f2. f1 ⊆ ⫱f2 → ⫯f1 ⊆ f2.
#f1 #f2 elim (gr_map_split_tl f2) #H #Hf12
/2 width=5 by gr_sle_push, gr_sle_weak/
qed-.
