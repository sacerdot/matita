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

include "ground/relocation/gr_after_eq.ma".

(* RELATIONAL COMPOSITION FOR GENERIC RELOCATION MAPS ***********************************************************)

(* Main properties **********************************************************)

(*** after_trans1 *)
corec theorem gr_after_trans_sn:
              ∀f0,f3,f4. f0 ⊚ f3 ≘ f4 →
              ∀f1,f2. f1 ⊚ f2 ≘ f0 →
              ∀f. f2 ⊚ f3 ≘ f → f1 ⊚ f ≘ f4.
#f0 #f3 #f4 * -f0 -f3 -f4 #f0 #f3 #f4 #g0 [1,2: #g3 ] #g4
[ #Hf4 #H0 #H3 #H4 #g1 #g2 #Hg0 #g #Hg
  cases (gr_after_inv_push … Hg0 … H0) -g0
  #f1 #f2 #Hf0 #H1 #H2
  cases (gr_after_inv_push_bi … Hg … H2 H3) -g2 -g3
  #f #Hf #H /3 width=7 by gr_after_refl/
| #Hf4 #H0 #H3 #H4 #g1 #g2 #Hg0 #g #Hg
  cases (gr_after_inv_push … Hg0 … H0) -g0
  #f1 #f2 #Hf0 #H1 #H2
  cases (gr_after_inv_push_next … Hg … H2 H3) -g2 -g3
  #f #Hf #H /3 width=7 by gr_after_push/
| #Hf4 #H0 #H4 #g1 #g2 #Hg0 #g #Hg
  cases (gr_after_inv_next … Hg0 … H0) -g0 *
  [ #f1 #f2 #Hf0 #H1 #H2
    cases (gr_after_inv_next_sn … Hg … H2) -g2
    #f #Hf #H /3 width=7 by gr_after_push/
  | #f1 #Hf0 #H1 /3 width=6 by gr_after_next/
  ]
]
qed-.

(*** after_trans2 *)
corec theorem gr_after_trans_dx:
              ∀f1,f0,f4. f1 ⊚ f0 ≘ f4 →
              ∀f2, f3. f2 ⊚ f3 ≘ f0 →
              ∀f. f1 ⊚ f2 ≘ f → f ⊚ f3 ≘ f4.
#f1 #f0 #f4 * -f1 -f0 -f4 #f1 #f0 #f4 #g1 [1,2: #g0 ] #g4
[ #Hf4 #H1 #H0 #H4 #g2 #g3 #Hg0 #g #Hg
  cases (gr_after_inv_push … Hg0 … H0) -g0
  #f2 #f3 #Hf0 #H2 #H3
  cases (gr_after_inv_push_bi … Hg … H1 H2) -g1 -g2
  #f #Hf #H /3 width=7 by gr_after_refl/
| #Hf4 #H1 #H0 #H4 #g2 #g3 #Hg0 #g #Hg
  cases (gr_after_inv_next … Hg0 … H0) -g0 *
  [ #f2 #f3 #Hf0 #H2 #H3
    cases (gr_after_inv_push_bi … Hg … H1 H2) -g1 -g2
    #f #Hf #H /3 width=7 by gr_after_push/
  | #f2 #Hf0 #H2
    cases (gr_after_inv_push_next … Hg … H1 H2) -g1 -g2
    #f #Hf #H /3 width=6 by gr_after_next/
  ]
| #Hf4 #H1 #H4 #f2 #f3 #Hf0 #g #Hg
  cases (gr_after_inv_next_sn … Hg … H1) -g1
  #f #Hg #H /3 width=6 by gr_after_next/
]
qed-.

(* Main inversion lemmas ****************************************************)

(*** after_mono *)
corec theorem gr_after_mono:
              ∀f1,f2,x,y. f1 ⊚ f2 ≘ x → f1 ⊚ f2 ≘ y → x ≡ y.
#f1 #f2 #x #y * -f1 -f2 -x
#f1 #f2 #x #g1 [1,2: #g2 ] #g #Hx #H1 [1,2: #H2 ] #H0x #Hy
[ cases (gr_after_inv_push_bi … Hy … H1 H2) -g1 -g2 /3 width=8 by gr_eq_push/
| cases (gr_after_inv_push_next … Hy … H1 H2) -g1 -g2 /3 width=8 by gr_eq_next/
| cases (gr_after_inv_next_sn … Hy … H1) -g1 /3 width=8 by gr_eq_next/
]
qed-.

(*** after_mono_eq *)
lemma gr_after_mono_eq:
      ∀f1,f2,f. f1 ⊚ f2 ≘ f → ∀g1,g2,g. g1 ⊚ g2 ≘ g →
      f1 ≡ g1 → f2 ≡ g2 → f ≡ g.
/4 width=4 by gr_after_mono, gr_after_eq_repl_back_dx, gr_after_eq_repl_back_sn/ qed-.
