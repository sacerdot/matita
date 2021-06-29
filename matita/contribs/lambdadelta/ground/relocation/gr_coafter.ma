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

include "ground/notation/relations/rcoafter_3.ma".
include "ground/xoa/ex_3_2.ma".
include "ground/relocation/gr_tl.ma".

(* RELATIONAL CO-COMPOSITION FOR GENERIC RELOCATION MAPS ********************)

(*** coafter *)
coinductive gr_coafter: relation3 gr_map gr_map gr_map ≝
(*** coafter_refl *)
| gr_coafter_refl (f1) (f2) (f) (g1) (g2) (g):
  gr_coafter f1 f2 f → ⫯f1 = g1 → ⫯f2 = g2 → ⫯f = g → gr_coafter g1 g2 g
(*** coafter_push *)
| gr_coafter_push (f1) (f2) (f) (g1) (g2) (g):
  gr_coafter f1 f2 f → ⫯f1 = g1 → ↑f2 = g2 → ↑f = g → gr_coafter g1 g2 g
(*** coafter_next *)
| gr_coafter_next (f1) (f2) (f) (g1) (g):
  gr_coafter f1 f2 f → ↑f1 = g1 → ⫯f = g → gr_coafter g1 f2 g
.

interpretation
  "relational co-composition (generic relocation maps)"
  'RCoAfter f1 f2 f = (gr_coafter f1 f2 f).

(* Basic inversions *********************************************************)

(*** coafter_inv_ppx *)
lemma gr_coafter_inv_push_bi:
      ∀g1,g2,g. g1 ~⊚ g2 ≘ g → ∀f1,f2. ⫯f1 = g1 → ⫯f2 = g2 →
      ∃∃f. f1 ~⊚ f2 ≘ f & ⫯f = g.
#g1 #g2 #g * -g1 -g2 -g #f1 #f2 #f #g1
[ #g2 #g #Hf #H1 #H2 #H #x1 #x2 #Hx1 #Hx2 destruct
  >(eq_inv_gr_push_bi … Hx1) >(eq_inv_gr_push_bi … Hx2) -x2 -x1
  /2 width=3 by ex2_intro/
| #g2 #g #_ #_ #H2 #_ #x1 #x2 #_ #Hx2 destruct
  elim (eq_inv_gr_push_next … Hx2)
| #g #_ #H1 #_ #x1 #x2 #Hx1 #_ destruct
  elim (eq_inv_gr_push_next … Hx1)
]
qed-.

(*** coafter_inv_pnx *)
lemma gr_coafter_inv_push_next:
      ∀g1,g2,g. g1 ~⊚ g2 ≘ g → ∀f1,f2. ⫯f1 = g1 → ↑f2 = g2 →
      ∃∃f. f1 ~⊚ f2 ≘ f & ↑f = g.
#g1 #g2 #g * -g1 -g2 -g #f1 #f2 #f #g1
[ #g2 #g #_ #_ #H2 #_ #x1 #x2 #_ #Hx2 destruct
  elim (eq_inv_gr_next_push … Hx2)
| #g2 #g #Hf #H1 #H2 #H3 #x1 #x2 #Hx1 #Hx2 destruct
  >(eq_inv_gr_push_bi … Hx1) >(eq_inv_gr_next_bi … Hx2) -x2 -x1
  /2 width=3 by ex2_intro/
| #g #_ #H1 #_ #x1 #x2 #Hx1 #_ destruct
  elim (eq_inv_gr_push_next … Hx1)
]
qed-.

(*** coafter_inv_nxx *)
lemma gr_coafter_inv_next_sn:
      ∀g1,f2,g. g1 ~⊚ f2 ≘ g → ∀f1. ↑f1 = g1 →
      ∃∃f. f1 ~⊚ f2 ≘ f & ⫯f = g.
#g1 #f2 #g * -g1 -f2 -g #f1 #f2 #f #g1
[ #g2 #g #_ #H1 #_ #_ #x1 #Hx1 destruct
  elim (eq_inv_gr_next_push … Hx1)
| #g2 #g #_ #H1 #_ #_ #x1 #Hx1 destruct
  elim (eq_inv_gr_next_push … Hx1)
| #g #Hf #H1 #H #x1 #Hx1 destruct
  >(eq_inv_gr_next_bi … Hx1) -x1
  /2 width=3 by ex2_intro/
]
qed-.

(* Advanced inversions ******************************************************)

(*** coafter_inv_ppp *)
lemma gr_coafter_inv_push_bi_push:
      ∀g1,g2,g. g1 ~⊚ g2 ≘ g →
      ∀f1,f2,f. ⫯f1 = g1 → ⫯f2 = g2 → ⫯f = g → f1 ~⊚ f2 ≘ f.
#g1 #g2 #g #Hg #f1 #f2 #f #H1 #H2 #H
elim (gr_coafter_inv_push_bi … Hg … H1 H2) -g1 -g2 #x #Hf #Hx destruct
<(eq_inv_gr_push_bi … Hx) -f //
qed-.

(*** coafter_inv_ppn *)
lemma gr_coafter_inv_push_bi_next:
      ∀g1,g2,g. g1 ~⊚ g2 ≘ g →
      ∀f1,f2,f. ⫯f1 = g1 → ⫯f2 = g2 → ↑f = g → ⊥.
#g1 #g2 #g #Hg #f1 #f2 #f #H1 #H2 #H
elim (gr_coafter_inv_push_bi … Hg … H1 H2) -g1 -g2 #x #Hf #Hx destruct
elim (eq_inv_gr_push_next … Hx)
qed-.

(*** coafter_inv_pnn *)
lemma gr_coafter_inv_push_next_next:
      ∀g1,g2,g. g1 ~⊚ g2 ≘ g →
      ∀f1,f2,f. ⫯f1 = g1 → ↑f2 = g2 → ↑f = g → f1 ~⊚ f2 ≘ f.
#g1 #g2 #g #Hg #f1 #f2 #f #H1 #H2 #H
elim (gr_coafter_inv_push_next … Hg … H1 H2) -g1 -g2 #x #Hf #Hx destruct
<(eq_inv_gr_next_bi … Hx) -f //
qed-.

(*** coafter_inv_pnp *)
lemma gr_coafter_inv_push_next_push:
      ∀g1,g2,g. g1 ~⊚ g2 ≘ g →
      ∀f1,f2,f. ⫯f1 = g1 → ↑f2 = g2 → ⫯f = g → ⊥.
#g1 #g2 #g #Hg #f1 #f2 #f #H1 #H2 #H
elim (gr_coafter_inv_push_next … Hg … H1 H2) -g1 -g2 #x #Hf #Hx destruct
elim (eq_inv_gr_next_push … Hx)
qed-.

(*** coafter_inv_nxp *)
lemma gr_coafter_inv_next_sn_push:
      ∀g1,f2,g. g1 ~⊚ f2 ≘ g →
      ∀f1,f. ↑f1 = g1 → ⫯f = g → f1 ~⊚ f2 ≘ f.
#g1 #f2 #g #Hg #f1 #f #H1 #H
elim (gr_coafter_inv_next_sn … Hg … H1) -g1 #x #Hf #Hx destruct
<(eq_inv_gr_push_bi … Hx) -f //
qed-.

(*** coafter_inv_nxn *)
lemma gr_coafter_inv_next_sn_next:
      ∀g1,f2,g. g1 ~⊚ f2 ≘ g →
      ∀f1,f. ↑f1 = g1 → ↑f = g → ⊥.
#g1 #f2 #g #Hg #f1 #f #H1 #H
elim (gr_coafter_inv_next_sn … Hg … H1) -g1 #x #Hf #Hx destruct
elim (eq_inv_gr_push_next … Hx)
qed-.

(*** coafter_inv_pxp *)
lemma gr_coafter_inv_push_sn_push:
      ∀g1,g2,g. g1 ~⊚ g2 ≘ g →
      ∀f1,f. ⫯f1 = g1 → ⫯f = g →
      ∃∃f2. f1 ~⊚ f2 ≘ f & ⫯f2 = g2.
#g1 #g2 #g #Hg #f1 #f #H1 #H
elim (gr_map_split_tl g2) #H2
[ lapply (gr_coafter_inv_push_bi_push … Hg … H1 H2 H) -g1 -g
  /2 width=3 by ex2_intro/
| elim (gr_coafter_inv_push_next_push … Hg … H1 H2 H)
]
qed-.

(*** coafter_inv_pxn *)
lemma gr_coafter_inv_push_sn_next:
      ∀g1,g2,g. g1 ~⊚ g2 ≘ g →
      ∀f1,f. ⫯f1 = g1 → ↑f = g →
      ∃∃f2. f1 ~⊚ f2 ≘ f & ↑f2 = g2.
#g1 #g2 #g #Hg #f1 #f #H1 #H
elim (gr_map_split_tl g2) #H2
[ elim (gr_coafter_inv_push_bi_next … Hg … H1 H2 H)
| lapply (gr_coafter_inv_push_next_next … Hg … H1 … H) -g1 -g
  /2 width=3 by ex2_intro/
]
qed-.

(*** coafter_inv_xxn *)
lemma gr_coafter_inv_next:
      ∀g1,g2,g. g1 ~⊚ g2 ≘ g → ∀f. ↑f = g →
      ∃∃f1,f2. f1 ~⊚ f2 ≘ f & ⫯f1 = g1 & ↑f2 = g2.
#g1 #g2 #g #Hg #f #H
elim (gr_map_split_tl g1) #H1
[ elim (gr_coafter_inv_push_sn_next … Hg … H1 H) -g
  /2 width=5 by ex3_2_intro/
| elim (gr_coafter_inv_next_sn_next … Hg … H1 H)
]
qed-.

(*** coafter_inv_xnn *)
lemma gr_coafter_inv_next_dx_next:
      ∀g1,g2,g. g1 ~⊚ g2 ≘ g →
      ∀f2,f. ↑f2 = g2 → ↑f = g →
      ∃∃f1. f1 ~⊚ f2 ≘ f & ⫯f1 = g1.
#g1 #g2 #g #Hg #f2 #f #H2 destruct #H
elim (gr_coafter_inv_next … Hg … H) -g #z1 #z2 #Hf #H1 #H2 destruct
/2 width=3 by ex2_intro/
qed-.

(*** coafter_inv_xxp *)
lemma gr_coafter_inv_push:
      ∀g1,g2,g. g1 ~⊚ g2 ≘ g → ∀f. ⫯f = g →
      ∨∨ ∃∃f1,f2. f1 ~⊚ f2 ≘ f & ⫯f1 = g1 & ⫯f2 = g2
       | ∃∃f1. f1 ~⊚ g2 ≘ f & ↑f1 = g1.
#g1 #g2 #g #Hg #f #H
elim (gr_map_split_tl g1) #H1
[ elim (gr_coafter_inv_push_sn_push … Hg … H1 H) -g
  /3 width=5 by or_introl, ex3_2_intro/
| /4 width=5 by gr_coafter_inv_next_sn_push, or_intror, ex2_intro/
]
qed-.

(*** coafter_inv_pxx *)
lemma gr_coafter_inv_push_sn:
      ∀g1,g2,g. g1 ~⊚ g2 ≘ g → ∀f1. ⫯f1 = g1 →
      ∨∨ ∃∃f2,f. f1 ~⊚ f2 ≘ f & ⫯f2 = g2 & ⫯f = g
       | ∃∃f2,f. f1 ~⊚ f2 ≘ f & ↑f2 = g2 & ↑f = g.
#g1 #g2 #g #Hg #f1 #H1
elim (gr_map_split_tl g2) #H2
[ elim (gr_coafter_inv_push_bi … Hg … H1 H2) -g1
  /3 width=5 by or_introl, ex3_2_intro/
| elim (gr_coafter_inv_push_next … Hg … H1 H2) -g1
  /3 width=5 by or_intror, ex3_2_intro/
]
qed-.

(* Inversions with gr_tl ****************************************************)

(*** coafter_inv_tl1 *)
lemma gr_coafter_inv_tl_dx:
      ∀g2,g1,g. g2 ~⊚ ⫰g1 ≘ g →
      ∃∃f. ⫯g2 ~⊚ g1 ≘ f & ⫰f = g.
#g2 #g1 #g
elim (gr_map_split_tl g1) #H1 #H2
[ /3 width=7 by gr_coafter_refl, ex2_intro/
| @(ex2_intro … (↑g)) /2 width=7 by gr_coafter_push/ (* * full auto fails *)
]
qed-.

(*** coafter_inv_tl0 *)
lemma gr_coafter_inv_tl:
      ∀g2,g1,g. g2 ~⊚ g1 ≘ ⫰g →
      ∃∃f1. ⫯g2 ~⊚ f1 ≘ g & ⫰f1 = g1.
#g2 #g1 #g
elim (gr_map_split_tl g) #H1 #H2
[ /3 width=7 by gr_coafter_refl, ex2_intro/
| @(ex2_intro … (↑g1)) /2 width=7 by gr_coafter_push/ (* * full auto fails *)
]
qed-.
