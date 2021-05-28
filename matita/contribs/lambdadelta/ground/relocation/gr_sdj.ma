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

include "ground/notation/relations/parallel_2.ma".
include "ground/relocation/gr_tl.ma".

(* DISJOINTNESS FOR GENERIC RELOCATION MAPS ***********************************************************)

(*** sdj *)
coinductive gr_sdj: relation gr_map ≝
(*** sdj_pp *)
| gr_sdj_push_bi (f1) (f2) (g1) (g2):
  gr_sdj f1 f2 → ⫯f1 = g1 → ⫯f2 = g2 → gr_sdj g1 g2
(*** sdj_np *)
| gr_sdj_next_push (f1) (f2) (g1) (g2):
  gr_sdj f1 f2 → ↑f1 = g1 → ⫯f2 = g2 → gr_sdj g1 g2
(*** sdj_pn *)
| gr_sdj_push_next (f1) (f2) (g1) (g2):
  gr_sdj f1 f2 → ⫯f1 = g1 → ↑f2 = g2 → gr_sdj g1 g2
.

interpretation
  "disjointness (generic relocation maps)"
  'Parallel f1 f2 = (gr_sdj f1 f2).

(* Basic properties *********************************************************)

(*** sdj_sym *)
corec lemma gr_sdj_sym:
            symmetric … gr_sdj.
#f1 #f2 * -f1 -f2
#f1 #f2 #g1 #g2 #Hf #H1 #H2
[ @(gr_sdj_push_bi … H2 H1)
| @(gr_sdj_push_next … H2 H1)
| @(gr_sdj_next_push … H2 H1)
] -g2 -g1
/2 width=1 by/
qed-.

(* Basic inversion lemmas ***************************************************)

(*** sdj_inv_pp *)
lemma gr_sdj_inv_push_bi:
      ∀g1,g2. g1 ∥ g2 → ∀f1,f2. ⫯f1 = g1 → ⫯f2 = g2 → f1 ∥ f2.
#g1 #g2 * -g1 -g2
#f1 #f2 #g1 #g2 #H #H1 #H2 #x1 #x2 #Hx1 #Hx2 destruct
[ lapply (eq_inv_gr_push_bi … Hx1) -Hx1
  lapply (eq_inv_gr_push_bi … Hx2) -Hx2 //
| elim (eq_inv_gr_push_next … Hx1)
| elim (eq_inv_gr_push_next … Hx2)
]
qed-.

(*** sdj_inv_np *)
lemma gr_sdj_inv_next_push:
      ∀g1,g2. g1 ∥ g2 → ∀f1,f2. ↑f1 = g1 → ⫯f2 = g2 → f1 ∥ f2.
#g1 #g2 * -g1 -g2
#f1 #f2 #g1 #g2 #H #H1 #H2 #x1 #x2 #Hx1 #Hx2 destruct
[ elim (eq_inv_gr_next_push … Hx1)
| lapply (eq_inv_gr_next_bi … Hx1) -Hx1
  lapply (eq_inv_gr_push_bi … Hx2) -Hx2 //
| elim (eq_inv_gr_push_next … Hx2)
]
qed-.

(*** sdj_inv_pn *)
lemma gr_sdj_inv_push_next:
      ∀g1,g2. g1 ∥ g2 → ∀f1,f2. ⫯f1 = g1 → ↑f2 = g2 → f1 ∥ f2.
#g1 #g2 * -g1 -g2
#f1 #f2 #g1 #g2 #H #H1 #H2 #x1 #x2 #Hx1 #Hx2 destruct
[ elim (eq_inv_gr_next_push … Hx2)
| elim (eq_inv_gr_push_next … Hx1)
| lapply (eq_inv_gr_push_bi … Hx1) -Hx1
  lapply (eq_inv_gr_next_bi … Hx2) -Hx2 //
]
qed-.

(*** sdj_inv_nn *)
lemma gr_sdj_inv_next_bi:
      ∀g1,g2. g1 ∥ g2 → ∀f1,f2. ↑f1 = g1 → ↑f2 = g2 → ⊥.
#g1 #g2 * -g1 -g2
#f1 #f2 #g1 #g2 #H #H1 #H2 #x1 #x2 #Hx1 #Hx2 destruct
[ elim (eq_inv_gr_next_push … Hx1)
| elim (eq_inv_gr_next_push … Hx2)
| elim (eq_inv_gr_next_push … Hx1)
]
qed-.

(* Advanced inversion lemmas ************************************************)

(*** sdj_inv_nx *)
lemma gr_sdj_inv_next_sn:
      ∀g1,g2. g1 ∥ g2 → ∀f1. ↑f1 = g1 →
      ∃∃f2. f1 ∥ f2 & ⫯f2 = g2.
#g1 #g2 elim (gr_map_split_tl g2) #H2 #H #f1 #H1
[ lapply (gr_sdj_inv_next_push … H … H1 H2) -H /2 width=3 by ex2_intro/
| elim (gr_sdj_inv_next_bi … H … H1 H2)
]
qed-.

(*** sdj_inv_xn *)
lemma gr_sdj_inv_next_dx:
      ∀g1,g2. g1 ∥ g2 → ∀f2. ↑f2 = g2 →
      ∃∃f1. f1 ∥ f2 & ⫯f1 = g1.
#g1 #g2 elim (gr_map_split_tl g1) #H1 #H #f2 #H2
[ lapply (gr_sdj_inv_push_next … H … H1 H2) -H /2 width=3 by ex2_intro/
| elim (gr_sdj_inv_next_bi … H … H1 H2)
]
qed-.

(*** sdj_inv_xp *)
lemma gr_sdj_inv_push_dx:
      ∀g1,g2. g1 ∥ g2 → ∀f2. ⫯f2 = g2 →
      ∨∨ ∃∃f1. f1 ∥ f2 & ⫯f1 = g1
       | ∃∃f1. f1 ∥ f2 & ↑f1 = g1.
#g1 #g2 elim (gr_map_split_tl g1) #H1 #H #f2 #H2
[ lapply (gr_sdj_inv_push_bi … H … H1 H2)
| lapply (gr_sdj_inv_next_push … H … H1 H2)
] -H -H2
/3 width=3 by ex2_intro, or_introl, or_intror/
qed-.

(*** sdj_inv_px *)
lemma gr_sdj_inv_push_sn:
      ∀g1,g2. g1 ∥ g2 → ∀f1. ⫯f1 = g1 →
      ∨∨ ∃∃f2. f1 ∥ f2 & ⫯f2 = g2
       | ∃∃f2. f1 ∥ f2 & ↑f2 = g2.
#g1 #g2 elim (gr_map_split_tl g2) #H2 #H #f1 #H1
[ lapply (gr_sdj_inv_push_bi … H … H1 H2)
| lapply (gr_sdj_inv_push_next … H … H1 H2)
] -H -H1
/3 width=3 by ex2_intro, or_introl, or_intror/
qed-.
