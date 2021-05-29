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

include "ground/relocation/gr_tl_eq.ma".
include "ground/relocation/gr_after.ma".

(* RELATIONAL COMPOSITION FOR GENERIC RELOCATION MAPS ***********************)

(* Constructions with gr_eq *************************************************)

(*** after_eq_repl_back2 *)
corec lemma gr_after_eq_repl_back_sn:
            ∀f1,f. gr_eq_repl_back (λf2. f2 ⊚ f1 ≘ f).
#f1 #f #f2 * -f2 -f1 -f
#f21 #f1 #f #g21 [1,2: #g1 ] #g #Hf #H21 [1,2: #H1 ] #H #g22 #H0
[ cases (gr_eq_inv_push_sn …  H0 …  H21) -g21 /3 width=7 by gr_after_refl/
| cases (gr_eq_inv_push_sn …  H0 …  H21) -g21 /3 width=7 by gr_after_push/
| cases (gr_eq_inv_next_sn …  H0 …  H21) -g21 /3 width=5 by gr_after_next/
]
qed-.

(*** after_eq_repl_fwd2 *)
lemma gr_after_eq_repl_fwd_sn:
      ∀f1,f. gr_eq_repl_fwd (λf2. f2 ⊚ f1 ≘ f).
#f1 #f @gr_eq_repl_sym /2 width=3 by gr_after_eq_repl_back_sn/
qed-.

(*** after_eq_repl_back1 *)
corec lemma gr_after_eq_repl_back_dx:
            ∀f2,f. gr_eq_repl_back (λf1. f2 ⊚ f1 ≘ f).
#f2 #f #f1 * -f2 -f1 -f
#f2 #f11 #f #g2 [1,2: #g11 ] #g #Hf #H2 [1,2: #H11 ] #H #g2 #H0
[ cases (gr_eq_inv_push_sn …  H0 …  H11) -g11 /3 width=7 by gr_after_refl/
| cases (gr_eq_inv_next_sn …  H0 …  H11) -g11 /3 width=7 by gr_after_push/
| @(gr_after_next … H2 H) /2 width=5 by/
]
qed-.

(*** after_eq_repl_fwd1 *)
lemma gr_after_eq_repl_fwd_dx:
      ∀f2,f. gr_eq_repl_fwd (λf1. f2 ⊚ f1 ≘ f).
#f2 #f @gr_eq_repl_sym /2 width=3 by gr_after_eq_repl_back_dx/
qed-.

(*** after_eq_repl_back0 *)
corec lemma gr_after_eq_repl_back:
            ∀f1,f2. gr_eq_repl_back (λf. f2 ⊚ f1 ≘ f).
#f2 #f1 #f * -f2 -f1 -f
#f2 #f1 #f01 #g2 [1,2: #g1 ] #g01 #Hf01 #H2 [1,2: #H1 ] #H01 #g02 #H0
[ cases (gr_eq_inv_push_sn …  H0 …  H01) -g01 /3 width=7 by gr_after_refl/
| cases (gr_eq_inv_next_sn …  H0 …  H01) -g01 /3 width=7 by gr_after_push/
| cases (gr_eq_inv_next_sn …  H0 …  H01) -g01 /3 width=5 by gr_after_next/
]
qed-.

(*** after_eq_repl_fwd0 *)
lemma gr_after_eq_repl_fwd:
      ∀f2,f1. gr_eq_repl_fwd (λf. f2 ⊚ f1 ≘ f).
#f2 #f1 @gr_eq_repl_sym /2 width=3 by gr_after_eq_repl_back/
qed-.
