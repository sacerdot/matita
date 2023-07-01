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

include "ground/notation/relations/rafter_3.ma".
include "ground/xoa/ex_3_2.ma". 
include "ground/relocation/p1/pr_tl.ma".

(* RELATIONAL COMPOSITION FOR PARTIAL RELOCATION MAPS ***********************)

(*** after *)
coinductive pr_after: relation3 pr_map pr_map pr_map ≝
(*** after_refl *)
| pr_after_refl (f1) (f2) (f) (g1) (g2) (g):
  pr_after f1 f2 f → ⫯f1 = g1 → ⫯f2 = g2 → ⫯f = g → pr_after g1 g2 g
(*** after_push *)
| pr_after_push (f1) (f2) (f) (g1) (g2) (g):
  pr_after f1 f2 f → ⫯f1 = g1 → ↑f2 = g2 → ↑f = g → pr_after g1 g2 g
(*** after_next *)
| pr_after_next (f1) (f2) (f) (g1) (g):
  pr_after f1 f2 f → ↑f1 = g1 → ↑f = g → pr_after g1 f2 g
.

interpretation
  "relational composition (partial relocation maps)"
  'RAfter f1 f2 f = (pr_after f1 f2 f).

(* Basic inversions *********************************************************)

(*** after_inv_ppx *)
lemma pr_after_inv_push_bi:
      ∀g1,g2,g. g1 ⊚ g2 ≘ g → ∀f1,f2. ⫯f1 = g1 → ⫯f2 = g2 →
      ∃∃f. f1 ⊚ f2 ≘ f & ⫯f = g.
#g1 #g2 #g * -g1 -g2 -g #f1 #f2 #f #g1
[ #g2 #g #Hf #H1 #H2 #H #x1 #x2 #Hx1 #Hx2 destruct
  >(eq_inv_pr_push_bi … Hx1) >(eq_inv_pr_push_bi … Hx2) -x2 -x1
  /2 width=3 by ex2_intro/
| #g2 #g #_ #_ #H2 #_ #x1 #x2 #_ #Hx2 destruct
  elim (eq_inv_pr_push_next … Hx2)
| #g #_ #H1 #_ #x1 #x2 #Hx1 #_ destruct
  elim (eq_inv_pr_push_next … Hx1)
]
qed-.

(*** after_inv_pnx *)
lemma pr_after_inv_push_next:
      ∀g1,g2,g. g1 ⊚ g2 ≘ g → ∀f1,f2. ⫯f1 = g1 → ↑f2 = g2 →
      ∃∃f. f1 ⊚ f2 ≘ f & ↑f = g.
#g1 #g2 #g * -g1 -g2 -g #f1 #f2 #f #g1
[ #g2 #g #_ #_ #H2 #_ #x1 #x2 #_ #Hx2 destruct
  elim (eq_inv_pr_next_push … Hx2)
| #g2 #g #Hf #H1 #H2 #H3 #x1 #x2 #Hx1 #Hx2 destruct
  >(eq_inv_pr_push_bi … Hx1) >(eq_inv_pr_next_bi … Hx2) -x2 -x1
  /2 width=3 by ex2_intro/
| #g #_ #H1 #_ #x1 #x2 #Hx1 #_ destruct
  elim (eq_inv_pr_push_next … Hx1)
]
qed-.

(*** after_inv_nxx *)
lemma pr_after_inv_next_sn:
      ∀g1,f2,g. g1 ⊚ f2 ≘ g → ∀f1. ↑f1 = g1 →
      ∃∃f. f1 ⊚ f2 ≘ f & ↑f = g.
#g1 #f2 #g * -g1 -f2 -g #f1 #f2 #f #g1
[ #g2 #g #_ #H1 #_ #_ #x1 #Hx1 destruct
  elim (eq_inv_pr_next_push … Hx1)
| #g2 #g #_ #H1 #_ #_ #x1 #Hx1 destruct
  elim (eq_inv_pr_next_push … Hx1)
| #g #Hf #H1 #H #x1 #Hx1 destruct
  >(eq_inv_pr_next_bi … Hx1) -x1
  /2 width=3 by ex2_intro/
]
qed-.

(* Advanced inversions ******************************************************)

(*** after_inv_ppp *)
lemma pr_after_inv_push_bi_push:
      ∀g1,g2,g. g1 ⊚ g2 ≘ g →
      ∀f1,f2,f. ⫯f1 = g1 → ⫯f2 = g2 → ⫯f = g → f1 ⊚ f2 ≘ f.
#g1 #g2 #g #Hg #f1 #f2 #f #H1 #H2 #H elim (pr_after_inv_push_bi … Hg … H1 H2) -g1 -g2
#x #Hf #Hx destruct <(eq_inv_pr_push_bi … Hx) -f //
qed-.

(*** after_inv_ppn *)
lemma pr_after_inv_push_bi_next:
      ∀g1,g2,g. g1 ⊚ g2 ≘ g →
      ∀f1,f2,f. ⫯f1 = g1 → ⫯f2 = g2 → ↑f = g → ⊥.
#g1 #g2 #g #Hg #f1 #f2 #f #H1 #H2 #H elim (pr_after_inv_push_bi … Hg … H1 H2) -g1 -g2
#x #Hf #Hx destruct elim (eq_inv_pr_push_next … Hx)
qed-.

(*** after_inv_pnn *)
lemma pr_after_inv_push_next_next:
      ∀g1,g2,g. g1 ⊚ g2 ≘ g →
      ∀f1,f2,f. ⫯f1 = g1 → ↑f2 = g2 → ↑f = g → f1 ⊚ f2 ≘ f.
#g1 #g2 #g #Hg #f1 #f2 #f #H1 #H2 #H elim (pr_after_inv_push_next … Hg … H1 H2) -g1 -g2
#x #Hf #Hx destruct <(eq_inv_pr_next_bi … Hx) -f //
qed-.

(*** after_inv_pnp *)
lemma pr_after_inv_push_next_push:
      ∀g1,g2,g. g1 ⊚ g2 ≘ g →
      ∀f1,f2,f. ⫯f1 = g1 → ↑f2 = g2 → ⫯f = g → ⊥.
#g1 #g2 #g #Hg #f1 #f2 #f #H1 #H2 #H elim (pr_after_inv_push_next … Hg … H1 H2) -g1 -g2
#x #Hf #Hx destruct elim (eq_inv_pr_next_push … Hx)
qed-.

(*** after_inv_nxn *)
lemma pr_after_inv_next_sn_next:
      ∀g1,f2,g. g1 ⊚ f2 ≘ g →
      ∀f1,f. ↑f1 = g1 → ↑f = g → f1 ⊚ f2 ≘ f.
#g1 #f2 #g #Hg #f1 #f #H1 #H elim (pr_after_inv_next_sn … Hg … H1) -g1
#x #Hf #Hx destruct <(eq_inv_pr_next_bi … Hx) -f //
qed-.

(*** after_inv_nxp *)
lemma pr_after_inv_next_sn_push:
      ∀g1,f2,g. g1 ⊚ f2 ≘ g →
      ∀f1,f. ↑f1 = g1 → ⫯f = g → ⊥.
#g1 #f2 #g #Hg #f1 #f #H1 #H elim (pr_after_inv_next_sn … Hg … H1) -g1
#x #Hf #Hx destruct elim (eq_inv_pr_next_push … Hx)
qed-.

(*** after_inv_pxp *)
lemma pr_after_inv_push_sn_push:
      ∀g1,g2,g. g1 ⊚ g2 ≘ g →
      ∀f1,f. ⫯f1 = g1 → ⫯f = g →
      ∃∃f2. f1 ⊚ f2 ≘ f & ⫯f2 = g2.
#g1 #g2 elim (pr_map_split_tl g2)
#Hg2 #g #Hg #f1 #f #H1 #H
[ lapply (pr_after_inv_push_bi_push … Hg … H1 … H) -g1 -g
  /2 width=3 by ex2_intro/
| elim (pr_after_inv_push_next_push … Hg … H1 … H) -g1 -g -f1 -f //
]
qed-.

(*** after_inv_pxn *)
lemma pr_after_inv_push_sn_next:
      ∀g1,g2,g. g1 ⊚ g2 ≘ g →
      ∀f1,f. ⫯f1 = g1 → ↑f = g →
      ∃∃f2. f1 ⊚ f2 ≘ f & ↑f2 = g2.
#g1 #g2 elim (pr_map_split_tl g2)
#Hg2 #g #Hg #f1 #f #H1 #H
[ elim (pr_after_inv_push_bi_next … Hg … H1 … H) -g1 -g -f1 -f //
| lapply (pr_after_inv_push_next_next … Hg … H1 … H) -g1 -g
  /2 width=3 by ex2_intro/
]
qed-.

(*** after_inv_xxp *)
lemma pr_after_inv_push:
      ∀g1,g2,g. g1 ⊚ g2 ≘ g → ∀f. ⫯f = g →
      ∃∃f1,f2. f1 ⊚ f2 ≘ f & ⫯f1 = g1 & ⫯f2 = g2.
#g1 elim (pr_map_split_tl g1)
#Hg1 #g2 #g #Hg #f #H
[ elim (pr_after_inv_push_sn_push … Hg … H) -g /2 width=5 by ex3_2_intro/
| elim (pr_after_inv_next_sn_push … Hg … H) -g2 -g -f //
]
qed-.

(*** after_inv_xxn *)
lemma pr_after_inv_next:
      ∀g1,g2,g. g1 ⊚ g2 ≘ g → ∀f. ↑f = g →
      ∨∨ ∃∃f1,f2. f1 ⊚ f2 ≘ f & ⫯f1 = g1 & ↑f2 = g2
       | ∃∃f1. f1 ⊚ g2 ≘ f & ↑f1 = g1.
#g1 elim (pr_map_split_tl g1)
#Hg1 #g2 #g #Hg #f #H
[ elim (pr_after_inv_push_sn_next … Hg … H) -g
  /3 width=5 by or_introl, ex3_2_intro/
| /4 width=5 by pr_after_inv_next_sn_next, or_intror, ex2_intro/
]
qed-.

(*** after_inv_pxx *)
lemma pr_after_inv_push_sn:
      ∀g1,g2,g. g1 ⊚ g2 ≘ g → ∀f1. ⫯f1 = g1 →
      ∨∨ ∃∃f2,f. f1 ⊚ f2 ≘ f & ⫯f2 = g2 & ⫯f = g
       | ∃∃f2,f. f1 ⊚ f2 ≘ f & ↑f2 = g2 & ↑f = g.
#g1 #g2 elim (pr_map_split_tl g2)
#Hg2 #g #Hg #f1 #H
[ elim (pr_after_inv_push_bi … Hg … H) -g1
  /3 width=5 by or_introl, ex3_2_intro/
| elim (pr_after_inv_push_next … Hg … H) -g1
  /3 width=5 by or_intror, ex3_2_intro/
]
qed-.
