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

include "ground/relocation/gr_sle.ma".
(**) (* this should go first *)
include "ground/relocation/gr_tl_eq.ma".

(* INCLUSION FOR GENERIC RELOCATION MAPS ***********************************************************)

(* Properties with gr_eq *********************************************************)

(*** sle_eq_repl_back1 *)
corec lemma gr_sle_eq_repl_back_sn:
            ∀f2:gr_map. gr_eq_repl_back … (λf1:gr_map. f1 ⊆ f2).
#f2 #f1 * -f2 -f1
#f1 #f2 #g1 #g2 #Hf #H1 #H2 #g #H0
[ cases (gr_eq_inv_push_sn …  H0 …  H1) -g1 /3 width=5 by gr_sle_push/
| cases (gr_eq_inv_next_sn …  H0 …  H1) -g1 /3 width=5 by gr_sle_next/
| cases (gr_eq_inv_push_sn …  H0 …  H1) -g1 /3 width=5 by gr_sle_weak/
]
qed-.

(*** sle_eq_repl_fwd1 *)
lemma gr_sle_eq_repl_fwd_sn:
      ∀f2. gr_eq_repl_fwd … (λf1. f1 ⊆ f2).
#f2 @gr_eq_repl_sym /2 width=3 by gr_sle_eq_repl_back_sn/
qed-.

(*** sle_eq_repl_back2 *)
corec lemma gr_sle_eq_repl_back_dx:
            ∀f1. gr_eq_repl_back … (λf2. f1 ⊆ f2).
#f1 #f2 * -f1 -f2
#f1 #f2 #g1 #g2 #Hf #H1 #H2 #g #H0
[ cases (gr_eq_inv_push_sn …  H0 …  H2) -g2 /3 width=5 by gr_sle_push/
| cases (gr_eq_inv_next_sn …  H0 …  H2) -g2 /3 width=5 by gr_sle_next/
| cases (gr_eq_inv_next_sn …  H0 …  H2) -g2 /3 width=5 by gr_sle_weak/
]
qed-.

(*** sle_eq_repl_fwd2 *)
lemma gr_sle_eq_repl_fwd_dx:
      ∀f1. gr_eq_repl_fwd … (λf2. f1 ⊆ f2).
#f1 @gr_eq_repl_sym /2 width=3 by gr_sle_eq_repl_back_dx/
qed-.

(*** sle_refl_eq *)
lemma gr_sle_refl_eq:
      ∀f1,f2. f1 ≡ f2 → f1 ⊆ f2.
/2 width=3 by gr_sle_eq_repl_back_dx/ qed.
