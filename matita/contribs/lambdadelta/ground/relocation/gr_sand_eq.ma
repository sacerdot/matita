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
include "ground/relocation/gr_sand.ma".

(* RELATIONAL INTERSECTION FOR GENERIC RELOCATION MAPS **********************)

(* Constructions with gr_eq *************************************************)

(*** sand_eq_repl_back1 *)
corec lemma gr_sand_eq_repl_back_sn:
            ∀f2,f. gr_eq_repl_back … (λf1. f1 ⋒ f2 ≘ f).
#f2 #f #f1 * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H0 #x #Hx
try cases (gr_eq_inv_push_sn … Hx … H1) try cases (gr_eq_inv_next_sn … Hx … H1) -g1
/3 width=7 by gr_sand_push_bi, gr_sand_next_push, gr_sand_push_next, gr_sand_next_bi/
qed-.

(*** sand_eq_repl_fwd1 *)
lemma gr_sand_eq_repl_fwd_sn:
      ∀f2,f. gr_eq_repl_fwd … (λf1. f1 ⋒ f2 ≘ f).
#f2 #f @gr_eq_repl_sym /2 width=3 by gr_sand_eq_repl_back_sn/
qed-.

(*** sand_eq_repl_back2 *)
corec lemma gr_sand_eq_repl_back_dx:
            ∀f1,f. gr_eq_repl_back … (λf2. f1 ⋒ f2 ≘ f).
#f1 #f #f2 * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf #H #H2 #H0 #x #Hx
try cases (gr_eq_inv_push_sn … Hx … H2) try cases (gr_eq_inv_next_sn … Hx … H2) -g2
/3 width=7 by gr_sand_push_bi, gr_sand_next_push, gr_sand_push_next, gr_sand_next_bi/
qed-.

(*** sand_eq_repl_fwd2 *)
lemma sand_eq_repl_fwd_dx:
      ∀f1,f. gr_eq_repl_fwd … (λf2. f1 ⋒ f2 ≘ f).
#f1 #f @gr_eq_repl_sym /2 width=3 by gr_sand_eq_repl_back_dx/
qed-.

(*** sand_eq_repl_back3 *)
corec lemma gr_sand_eq_repl_back:
            ∀f1,f2. gr_eq_repl_back … (λf. f1 ⋒ f2 ≘ f).
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf #H #H2 #H0 #x #Hx
try cases (gr_eq_inv_push_sn … Hx … H0) try cases (gr_eq_inv_next_sn … Hx … H0) -g
/3 width=7 by gr_sand_push_bi, gr_sand_next_push, gr_sand_push_next, gr_sand_next_bi/
qed-.

(*** sand_eq_repl_fwd3 *)
lemma gr_sand_eq_repl_fwd:
      ∀f1,f2. gr_eq_repl_fwd … (λf. f1 ⋒ f2 ≘ f).
#f1 #f2 @gr_eq_repl_sym /2 width=3 by gr_sand_eq_repl_back/
qed-.
