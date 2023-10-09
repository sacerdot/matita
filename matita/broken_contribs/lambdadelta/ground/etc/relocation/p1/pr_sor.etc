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

include "ground/notation/relations/runion_3.ma".
include "ground/xoa/or_3.ma".
include "ground/xoa/ex_3_2.ma".
include "ground/relocation/p1/pr_tl.ma".

(* RELATIONAL UNION FOR PARTIAL RELOCATION MAPS *****************************)

(*** sor *)
coinductive pr_sor: relation3 pr_map pr_map pr_map ≝
(*** sor_pp *)
| pr_sor_push_bi (f1) (f2) (f) (g1) (g2) (g):
  pr_sor f1 f2 f → ⫯f1 = g1 → ⫯f2 = g2 → ⫯f = g → pr_sor g1 g2 g
(*** sor_np *)
| pr_sor_next_push (f1) (f2) (f) (g1) (g2) (g):
  pr_sor f1 f2 f → ↑f1 = g1 → ⫯f2 = g2 → ↑f = g → pr_sor g1 g2 g
(*** sor_pn *)
| pr_sor_push_next (f1) (f2) (f) (g1) (g2) (g):
  pr_sor f1 f2 f → ⫯f1 = g1 → ↑f2 = g2 → ↑f = g → pr_sor g1 g2 g
(*** sor_nn *)
| pr_sor_next_bi (f1) (f2) (f) (g1) (g2) (g):
  pr_sor f1 f2 f → ↑f1 = g1 → ↑f2 = g2 → ↑f = g → pr_sor g1 g2 g
.

interpretation
  "relational union (partial relocation maps)"
  'RUnion f1 f2 f = (pr_sor f1 f2 f).

(* Basic constructions ******************************************************)

(*** sor_idem *)
corec lemma pr_sor_idem:
            ∀f. f ⋓ f ≘ f.
#f cases (pr_map_split_tl f) #H
[ @(pr_sor_push_bi … H H H)
| @(pr_sor_next_bi … H H H)
] -H //
qed.

(*** sor_comm *)
corec lemma pr_sor_comm:
            ∀f1,f2,f. f1 ⋓ f2 ≘ f → f2 ⋓ f1 ≘ f.
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf * * * -g1 -g2 -g
[ @pr_sor_push_bi | @pr_sor_push_next | @pr_sor_next_push | @pr_sor_next_bi ] /2 width=7 by/
qed-.

(* Basic inversions *********************************************************)

(*** sor_inv_ppx *)
lemma pr_sor_inv_push_bi:
      ∀g1,g2,g. g1 ⋓ g2 ≘ g → ∀f1,f2. ⫯f1 = g1 → ⫯f2 = g2 →
      ∃∃f. f1 ⋓ f2 ≘ f & ⫯f = g.
#g1 #g2 #g * -g1 -g2 -g
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #x1 #x2 #Hx1 #Hx2 destruct
try (>(eq_inv_pr_push_bi … Hx1) -x1) try (>(eq_inv_pr_next_bi … Hx1) -x1)
try elim (eq_inv_pr_push_next … Hx1) try elim (eq_inv_pr_next_push … Hx1)
try (>(eq_inv_pr_push_bi … Hx2) -x2) try (>(eq_inv_pr_next_bi … Hx2) -x2)
try elim (eq_inv_pr_push_next … Hx2) try elim (eq_inv_pr_next_push … Hx2)
/2 width=3 by ex2_intro/
qed-.

(*** sor_inv_npx *)
lemma pr_sor_inv_next_push:
      ∀g1,g2,g. g1 ⋓ g2 ≘ g → ∀f1,f2. ↑f1 = g1 → ⫯f2 = g2 →
      ∃∃f. f1 ⋓ f2 ≘ f & ↑f = g.
#g1 #g2 #g * -g1 -g2 -g
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #x1 #x2 #Hx1 #Hx2 destruct
try (>(eq_inv_pr_push_bi … Hx1) -x1) try (>(eq_inv_pr_next_bi … Hx1) -x1)
try elim (eq_inv_pr_push_next … Hx1) try elim (eq_inv_pr_next_push … Hx1)
try (>(eq_inv_pr_push_bi … Hx2) -x2) try (>(eq_inv_pr_next_bi … Hx2) -x2)
try elim (eq_inv_pr_push_next … Hx2) try elim (eq_inv_pr_next_push … Hx2)
/2 width=3 by ex2_intro/
qed-.

(*** sor_inv_pnx *)
lemma pr_sor_inv_push_next:
      ∀g1,g2,g. g1 ⋓ g2 ≘ g → ∀f1,f2. ⫯f1 = g1 → ↑f2 = g2 →
      ∃∃f. f1 ⋓ f2 ≘ f & ↑f = g.
#g1 #g2 #g * -g1 -g2 -g
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #x1 #x2 #Hx1 #Hx2 destruct
try (>(eq_inv_pr_push_bi … Hx1) -x1) try (>(eq_inv_pr_next_bi … Hx1) -x1)
try elim (eq_inv_pr_push_next … Hx1) try elim (eq_inv_pr_next_push … Hx1)
try (>(eq_inv_pr_push_bi … Hx2) -x2) try (>(eq_inv_pr_next_bi … Hx2) -x2)
try elim (eq_inv_pr_push_next … Hx2) try elim (eq_inv_pr_next_push … Hx2)
/2 width=3 by ex2_intro/
qed-.

(*** sor_inv_nnx *)
lemma pr_sor_inv_next_bi:
      ∀g1,g2,g. g1 ⋓ g2 ≘ g → ∀f1,f2. ↑f1 = g1 → ↑f2 = g2 →
      ∃∃f. f1 ⋓ f2 ≘ f & ↑f = g.
#g1 #g2 #g * -g1 -g2 -g
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #x1 #x2 #Hx1 #Hx2 destruct
try (>(eq_inv_pr_push_bi … Hx1) -x1) try (>(eq_inv_pr_next_bi … Hx1) -x1)
try elim (eq_inv_pr_push_next … Hx1) try elim (eq_inv_pr_next_push … Hx1)
try (>(eq_inv_pr_push_bi … Hx2) -x2) try (>(eq_inv_pr_next_bi … Hx2) -x2)
try elim (eq_inv_pr_push_next … Hx2) try elim (eq_inv_pr_next_push … Hx2)
/2 width=3 by ex2_intro/
qed-.

(* Advanced inversions ******************************************************)

(*** sor_inv_ppn *)
lemma pr_sor_inv_push_bi_next:
      ∀g1,g2,g. g1 ⋓ g2 ≘ g →
      ∀f1,f2,f. ⫯f1 = g1 → ⫯f2 = g2 → ↑f = g → ⊥.
#g1 #g2 #g #H #f1 #f2 #f #H1 #H2 #H0
elim (pr_sor_inv_push_bi … H … H1 H2) -g1 -g2 #x #_ #H destruct
/2 width=3 by eq_inv_pr_push_next/
qed-.

(*** sor_inv_nxp *)
lemma pr_sor_inv_next_sn_push:
      ∀g1,g2,g. g1 ⋓ g2 ≘ g →
      ∀f1,f. ↑f1 = g1 → ⫯f = g → ⊥.
#g1 #g2 #g #H #f1 #f #H1 #H0
elim (pr_map_split_tl g2) #H2
[ elim (pr_sor_inv_next_push … H … H1 H2)
| elim (pr_sor_inv_next_bi … H … H1 H2)
] -g1 #x #H
/2 width=3 by eq_inv_pr_next_push/
qed-.

(*** sor_inv_xnp *)
lemma pr_sor_inv_next_dx_push:
      ∀g1,g2,g. g1 ⋓ g2 ≘ g →
      ∀f2,f. ↑f2 = g2 → ⫯f = g → ⊥.
#g1 #g2 #g #H #f2 #f #H2 #H0
elim (pr_map_split_tl g1) #H1
[ elim (pr_sor_inv_push_next … H … H1 H2)
| elim (pr_sor_inv_next_bi … H … H1 H2)
] -g2 #x #H
/2 width=3 by eq_inv_pr_next_push/
qed-.

(*** sor_inv_ppp *)
lemma pr_sor_inv_push_bi_push:
      ∀g1,g2,g. g1 ⋓ g2 ≘ g →
      ∀f1,f2,f. ⫯f1 = g1 → ⫯f2 = g2 → ⫯f = g → f1 ⋓ f2 ≘ f.
#g1 #g2 #g #H #f1 #f2 #f #H1 #H2 #H0
elim (pr_sor_inv_push_bi … H … H1 H2) -g1 -g2 #x #Hx #H destruct
<(eq_inv_pr_push_bi … H) -f //
qed-.

(*** sor_inv_npn *)
lemma pr_sor_inv_next_push_next:
      ∀g1,g2,g. g1 ⋓ g2 ≘ g →
      ∀f1,f2,f. ↑f1 = g1 → ⫯f2 = g2 → ↑f = g → f1 ⋓ f2 ≘ f.
#g1 #g2 #g #H #f1 #f2 #f #H1 #H2 #H0
elim (pr_sor_inv_next_push … H … H1 H2) -g1 -g2 #x #Hx #H destruct
<(eq_inv_pr_next_bi … H) -f //
qed-.

(*** sor_inv_pnn *)
lemma pr_sor_inv_push_next_next:
      ∀g1,g2,g. g1 ⋓ g2 ≘ g →
      ∀f1,f2,f. ⫯f1 = g1 → ↑f2 = g2 → ↑f = g → f1 ⋓ f2 ≘ f.
#g1 #g2 #g #H #f1 #f2 #f #H1 #H2 #H0
elim (pr_sor_inv_push_next … H … H1 H2) -g1 -g2 #x #Hx #H destruct
<(eq_inv_pr_next_bi … H) -f //
qed-.

(*** sor_inv_nnn *)
lemma pr_sor_inv_next_bi_next:
      ∀g1,g2,g. g1 ⋓ g2 ≘ g →
      ∀f1,f2,f. ↑f1 = g1 → ↑f2 = g2 → ↑f = g → f1 ⋓ f2 ≘ f.
#g1 #g2 #g #H #f1 #f2 #f #H1 #H2 #H0
elim (pr_sor_inv_next_bi … H … H1 H2) -g1 -g2 #x #Hx #H destruct
<(eq_inv_pr_next_bi … H) -f //
qed-.

(*** sor_inv_pxp *)
lemma pr_sor_inv_push_sn_push:
      ∀g1,g2,g. g1 ⋓ g2 ≘ g →
      ∀f1,f. ⫯f1 = g1 → ⫯f = g →
      ∃∃f2. f1 ⋓ f2 ≘ f & ⫯f2 = g2.
#g1 #g2 #g #H #f1 #f #H1 #H0
elim (pr_map_split_tl g2) #H2
[ /3 width=7 by pr_sor_inv_push_bi_push, ex2_intro/
| elim (pr_sor_inv_next_dx_push … H … H2 H0)
]
qed-.

(*** sor_inv_xpp *)
lemma pr_sor_inv_push_dx_push:
      ∀g1,g2,g. g1 ⋓ g2 ≘ g →
      ∀f2,f. ⫯f2 = g2 → ⫯f = g →
      ∃∃f1. f1 ⋓ f2 ≘ f & ⫯f1 = g1.
#g1 #g2 #g #H #f2 #f #H2 #H0
elim (pr_map_split_tl g1) #H1
[ /3 width=7 by pr_sor_inv_push_bi_push, ex2_intro/
| elim (pr_sor_inv_next_sn_push … H … H1 H0)
]
qed-.

(*** sor_inv_pxn *)
lemma pr_sor_inv_push_sn_next:
      ∀g1,g2,g. g1 ⋓ g2 ≘ g →
      ∀f1,f. ⫯f1 = g1 → ↑f = g →
      ∃∃f2. f1 ⋓ f2 ≘ f & ↑f2 = g2.
#g1 #g2 #g #H #f1 #f #H1 #H0
elim (pr_map_split_tl g2) #H2
[ elim (pr_sor_inv_push_bi_next … H … H1 H2 H0)
| /3 width=7 by pr_sor_inv_push_next_next, ex2_intro/
]
qed-.

(*** sor_inv_xpn *)
lemma pr_sor_inv_push_dx_next:
      ∀g1,g2,g. g1 ⋓ g2 ≘ g →
      ∀f2,f. ⫯f2 = g2 → ↑f = g →
      ∃∃f1. f1 ⋓ f2 ≘ f & ↑f1 = g1.
#g1 #g2 #g #H #f2 #f #H2 #H0
elim (pr_map_split_tl g1) #H1
[ elim (pr_sor_inv_push_bi_next … H … H1 H2 H0)
| /3 width=7 by pr_sor_inv_next_push_next, ex2_intro/
]
qed-.

(*** sor_inv_xxp *)
lemma pr_sor_inv_push:
      ∀g1,g2,g. g1 ⋓ g2 ≘ g → ∀f. ⫯f = g →
      ∃∃f1,f2. f1 ⋓ f2 ≘ f & ⫯f1 = g1 & ⫯f2 = g2.
#g1 #g2 #g #H #f #H0
elim (pr_map_split_tl g1) #H1
[ elim (pr_sor_inv_push_sn_push … H … H1 H0) -g /2 width=5 by ex3_2_intro/
| elim (pr_sor_inv_next_sn_push … H … H1 H0)
]
qed-.

(*** sor_inv_nxn *)
lemma pr_sor_inv_next_sn_next:
      ∀g1,g2,g. g1 ⋓ g2 ≘ g →
      ∀f1,f. ↑f1 = g1 → ↑f = g →
      ∨∨ ∃∃f2. f1 ⋓ f2 ≘ f & ⫯f2 = g2
       | ∃∃f2. f1 ⋓ f2 ≘ f & ↑f2 = g2.
#g1 #g2 elim (pr_map_split_tl g2)
/4 width=7 by pr_sor_inv_next_push_next, pr_sor_inv_next_bi_next, ex2_intro, or_intror, or_introl/
qed-.

(*** sor_inv_xnn *)
lemma pr_sor_inv_next_dx_next:
      ∀g1,g2,g. g1 ⋓ g2 ≘ g →
      ∀f2,f. ↑f2 = g2 → ↑f = g →
      ∨∨ ∃∃f1. f1 ⋓ f2 ≘ f & ⫯f1 = g1
       | ∃∃f1. f1 ⋓ f2 ≘ f & ↑f1 = g1.
#g1 elim (pr_map_split_tl g1)
/4 width=7 by pr_sor_inv_push_next_next, pr_sor_inv_next_bi_next, ex2_intro, or_intror, or_introl/
qed-.

(*** sor_inv_xxn *)
lemma pr_sor_inv_next:
      ∀g1,g2,g. g1 ⋓ g2 ≘ g → ∀f. ↑f = g →
      ∨∨ ∃∃f1,f2. f1 ⋓ f2 ≘ f & ↑f1 = g1 & ⫯f2 = g2
       | ∃∃f1,f2. f1 ⋓ f2 ≘ f & ⫯f1 = g1 & ↑f2 = g2
       | ∃∃f1,f2. f1 ⋓ f2 ≘ f & ↑f1 = g1 & ↑f2 = g2.
#g1 #g2 #g #H #f #H0
elim (pr_map_split_tl g1) #H1
[ elim (pr_sor_inv_push_sn_next … H … H1 H0) -g
  /3 width=5 by or3_intro1, ex3_2_intro/
| elim (pr_sor_inv_next_sn_next … H … H1 H0) -g *
  /3 width=5 by or3_intro0, or3_intro2, ex3_2_intro/
]
qed-.

(* Constructions with pr_tl *************************************************)

(*** sor_tl *)
lemma pr_sor_tl:
      ∀f1,f2,f. f1 ⋓ f2 ≘ f → ⫰f1 ⋓ ⫰f2 ≘ ⫰f.
#f1 cases (pr_map_split_tl f1) #H1
#f2 cases (pr_map_split_tl f2) #H2
#f #Hf
[ cases (pr_sor_inv_push_bi … Hf … H1 H2)
| cases (pr_sor_inv_push_next … Hf … H1 H2)
| cases (pr_sor_inv_next_push … Hf … H1 H2)
| cases (pr_sor_inv_next_bi … Hf … H1 H2)
] -Hf #g #Hg #H destruct //
qed.

(*** sor_xxn_tl *)
lemma pr_sor_next_tl:
      ∀g1,g2,g. g1 ⋓ g2 ≘ g → ∀f. ↑f = g →
      (∃∃f1,f2. f1 ⋓ f2 ≘ f & ↑f1 = g1 & ⫰g2 = f2) ∨
      (∃∃f1,f2. f1 ⋓ f2 ≘ f & ⫰g1 = f1 & ↑f2 = g2).
#g1 #g2 #g #H #f #H0 elim (pr_sor_inv_next … H … H0) -H -H0 *
/3 width=5 by ex3_2_intro, or_introl, or_intror/
qed-.

(*** sor_xnx_tl *)
lemma pr_sor_next_dx_tl:
      ∀g1,g2,g. g1 ⋓ g2 ≘ g → ∀f2. ↑f2 = g2 →
      ∃∃f1,f. f1 ⋓ f2 ≘ f & ⫰g1 = f1 & ↑f = g.
#g1 elim (pr_map_split_tl g1) #H1 #g2 #g #H #f2 #H2
[ elim (pr_sor_inv_push_next … H … H1 H2)
| elim (pr_sor_inv_next_bi … H … H1 H2)
] -g2
/3 width=5 by ex3_2_intro/
qed-.

(*** sor_nxx_tl *)
lemma pr_sor_next_sn_tl:
      ∀g1,g2,g. g1 ⋓ g2 ≘ g → ∀f1. ↑f1 = g1 →
      ∃∃f2,f. f1 ⋓ f2 ≘ f & ⫰g2 = f2 & ↑f = g.
#g1 #g2 elim (pr_map_split_tl g2) #H2 #g #H #f1 #H1
[ elim (pr_sor_inv_next_push … H … H1 H2)
| elim (pr_sor_inv_next_bi … H … H1 H2)
] -g1
/3 width=5 by ex3_2_intro/
qed-.

(* Inversions with pr_tl ****************************************************)

(*** sor_inv_tl_sn *)
lemma pr_sor_inv_tl_sn:
      ∀f1,f2,f. ⫰f1 ⋓ f2 ≘ f → f1 ⋓ ↑f2 ≘ ↑f.
#f1 #f2 #f elim (pr_map_split_tl f1)
/2 width=7 by pr_sor_push_next, pr_sor_next_bi/
qed-.

(*** sor_inv_tl_dx *)
lemma pr_sor_inv_tl_dx:
      ∀f1,f2,f. f1 ⋓ ⫰f2 ≘ f → ↑f1 ⋓ f2 ≘ ↑f.
#f1 #f2 #f elim (pr_map_split_tl f2)
/2 width=7 by pr_sor_next_push, pr_sor_next_bi/
qed-.
