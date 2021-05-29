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

include "ground/relocation/gr_eq.ma".
include "ground/relocation/gr_sor.ma".

(* RELATIONAL UNION FOR GENERIC RELOCATION MAPS *****************************)

(* Main inversions **********************************************************)

(*** sor_mono *)
corec theorem gr_sor_mono:
              ∀f1,f2,x,y. f1 ⋓ f2 ≘ x → f1 ⋓ f2 ≘ y → x ≡ y.
#f1 #f2 #x #y * -f1 -f2 -x
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #H
[ cases (gr_sor_inv_push_bi … H … H1 H2)
| cases (gr_sor_inv_next_push … H … H1 H2)
| cases (gr_sor_inv_push_next … H … H1 H2)
| cases (gr_sor_inv_next_bi … H … H1 H2)
] -g1 -g2
/3 width=5 by gr_eq_push, gr_eq_next/
qed-.

(* Main constructions *******************************************************)

(*** sor_assoc_dx *)
axiom gr_sor_assoc_dx:
      ∀f0,f3,f4. f0 ⋓ f3 ≘ f4 →
      ∀f1,f2. f1 ⋓ f2 ≘ f0 →
      ∀f. f2 ⋓ f3 ≘ f → f1 ⋓ f ≘ f4.

(*** sor_assoc_sn *)
axiom gr_sor_assoc_sn:
      ∀f1,f0,f4. f1 ⋓ f0 ≘ f4 →
      ∀f2, f3. f2 ⋓ f3 ≘ f0 →
      ∀f. f1 ⋓ f2 ≘ f → f ⋓ f3 ≘ f4.

(*** sor_comm_23 *)
lemma gr_sor_comm_23:
      ∀f0,f1,f2,f3,f4,f.
      f0⋓f4 ≘ f1 → f1⋓f2 ≘ f → f0⋓f2 ≘ f3 → f3⋓f4 ≘ f.
/4 width=6 by gr_sor_comm, gr_sor_assoc_dx/ qed-.

(*** sor_comm_23_idem *)
corec theorem gr_sor_comm_23_idem:
              ∀f0,f1,f2. f0 ⋓ f1 ≘ f2 →
              ∀f. f1 ⋓ f2 ≘ f → f1 ⋓ f0 ≘ f.
#f0 #f1 #f2 * -f0 -f1 -f2
#f0 #f1 #f2 #g0 #g1 #g2 #Hf2 #H0 #H1 #H2 #g #Hg
[ cases (gr_sor_inv_push_bi … Hg … H1 H2)
| cases (gr_sor_inv_push_next … Hg … H1 H2)
| cases (gr_sor_inv_next_bi … Hg … H1 H2)
| cases (gr_sor_inv_next_bi … Hg … H1 H2)
] -g2 #f #Hf #H
/3 width=7 by gr_sor_next_bi, gr_sor_next_push, gr_sor_push_next, gr_sor_push_bi/
qed-.

(*** sor_coll_dx *)
corec theorem gr_sor_coll_dx:
              ∀f1,f2,f. f1 ⋓ f2 ≘ f → ∀g1,g2,g. g1 ⋓ g2 ≘ g →
              ∀g0. g1 ⋓ g0 ≘ f1 → g2 ⋓ g0 ≘ f2 → g ⋓ g0 ≘ f.
#f1 #f2 #f cases (gr_map_split_tl f) #H1 #Hf #g1 #g2 #g #Hg #g0 #Hf1 #Hf2
[ cases (gr_sor_inv_push … Hf … H1) -Hf #x1 #x2 #Hf #Hx1 #Hx2
  cases (gr_sor_inv_push … Hf1 … Hx1) -f1 #y1 #y0 #Hf1 #Hy1 #Hy0
  cases (gr_sor_inv_push_dx_push … Hf2 … Hy0 … Hx2) -f2 #y2 #Hf2 #Hy2
  cases (gr_sor_inv_push_bi … Hg … Hy1 Hy2) -g1 -g2 #y #Hg #Hy
  @(gr_sor_push_bi … Hy Hy0 H1) -g -g0 /2 width=8 by/
| cases (gr_map_split_tl g) #H2
  [ cases (gr_sor_inv_push … Hg … H2) -Hg #y1 #y2 #Hg #Hy1 #Hy2
    cases (gr_sor_next_tl … Hf … H1) * #x1 #x2 #_ #Hx1 #Hx2
    [ cases (gr_sor_inv_push_sn_next … Hf1 … Hy1 Hx1) -g1 #y0 #Hf1 #Hy0
      cases (gr_sor_inv_push_next … Hf2 … Hy2 Hy0) -g2 -x2 #x2 #Hf2 #Hx2
    | cases (gr_sor_inv_push_sn_next … Hf2 … Hy2 Hx2) -g2 #y0 #Hf2 #Hy0
      cases (gr_sor_inv_push_next … Hf1 … Hy1 Hy0) -g1 -x1 #x1 #Hf1 #Hx1
    ]
    lapply (gr_sor_inv_next_bi_next … Hf … Hx1 Hx2 H1) -f1 -f2 #Hf
    @(gr_sor_push_next … H2 Hy0 H1) -g0 /2 width=8 by/
  | lapply (gr_sor_tl … Hf) -Hf #Hf
    lapply (gr_sor_tl … Hg) -Hg #Hg
    lapply (gr_sor_tl … Hf1) -Hf1 #Hf1
    lapply (gr_sor_tl … Hf2) -Hf2 #Hf2
    cases (gr_map_split_tl g0) #H0
    [ @(gr_sor_next_push … H2 H0 H1) /2 width=8 by/
    | @(gr_sor_next_bi … H2 H0 H1) /2 width=8 by/
    ]
  ]
]
qed-.

(*** sor_distr_dx *)
corec theorem gr_sor_distr_dx:
              ∀g0,g1,g2,g. g1 ⋓ g2 ≘ g →
              ∀f1,f2,f. g1 ⋓ g0 ≘ f1 → g2 ⋓ g0 ≘ f2 → g ⋓ g0 ≘ f →
              f1 ⋓ f2 ≘ f.
#g0 cases (gr_map_split_tl g0) #H0 #g1 #g2 #g
[ * -g1 -g2 -g #y1 #y2 #y #g1 #g2 #g #Hy #Hy1 #Hy2 #Hy #f1 #f2 #f #Hf1 #Hf2 #Hf
  [ cases (gr_sor_inv_push_bi … Hf1 … Hy1 H0) -g1
    cases (gr_sor_inv_push_bi … Hf2 … Hy2 H0) -g2
    cases (gr_sor_inv_push_bi … Hf … Hy H0) -g
  | cases (gr_sor_inv_next_push … Hf1 … Hy1 H0) -g1
    cases (gr_sor_inv_push_bi … Hf2 … Hy2 H0) -g2
    cases (gr_sor_inv_next_push … Hf … Hy H0) -g
  | cases (gr_sor_inv_push_bi … Hf1 … Hy1 H0) -g1
    cases (gr_sor_inv_next_push … Hf2 … Hy2 H0) -g2
    cases (gr_sor_inv_next_push … Hf … Hy H0) -g
  | cases (gr_sor_inv_next_push … Hf1 … Hy1 H0) -g1
    cases (gr_sor_inv_next_push … Hf2 … Hy2 H0) -g2
    cases (gr_sor_inv_next_push … Hf … Hy H0) -g
  ] #y #Hy #H #y2 #Hy2 #H2 #y1 #Hy1 #H1
  /3 width=8 by gr_sor_next_bi, gr_sor_next_push, gr_sor_push_next, gr_sor_push_bi/
| #H #f1 #f2 #f #Hf1 #Hf2 #Hf
  cases (gr_sor_next_dx_tl … Hf1 … H0) -Hf1
  cases (gr_sor_next_dx_tl … Hf2 … H0) -Hf2
  cases (gr_sor_next_dx_tl … Hf … H0) -Hf
  #y #x #Hx #Hy #H #y2 #x2 #Hx2 #Hy2 #H2 #y1 #x1 #Hx1 #Hy1 #H1
  /4 width=8 by gr_sor_tl, gr_sor_next_bi/
]
qed-.
