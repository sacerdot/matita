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
include "ground/relocation/gr_pat_lt.ma".

(* POSITIVE APPLICATION FOR GENERIC RELOCATION MAPS ***********************************************************)

(* Properties with gr_eq *)

(*** at_eq_repl_back *)
corec lemma gr_pat_eq_repl_back (i1) (i2):
            gr_eq_repl_back (λf. @❪i1,f❫ ≘ i2).
#f1 * -f1 -i1 -i2
[ #f1 #g1 #j1 #j2 #H #H1 #H2 #f2 #H12
  cases (gr_eq_inv_push_sn … H12 … H) -g1 /2 width=2 by gr_pat_refl/
| #f1 #i1 #i2 #Hf1 #g1 #j1 #j2 #H #H1 #H2 #f2 #H12
  cases (gr_eq_inv_push_sn … H12 … H) -g1 /3 width=7 by gr_pat_push/
| #f1 #i1 #i2 #Hf1 #g1 #j2 #H #H2 #f2 #H12
  cases (gr_eq_inv_next_sn … H12 … H) -g1 /3 width=5 by gr_pat_next/
]
qed-.

(*** at_eq_repl_fwd *)
lemma gr_pat_eq_repl_fwd (i1) (i2):
      gr_eq_repl_fwd (λf. @❪i1,f❫ ≘ i2).
#i1 #i2 @gr_eq_repl_sym /2 width=3 by gr_pat_eq_repl_back/
qed-.

lemma gr_pat_eq (f): ⫯f ≡ f → ∀i. @❪i,f❫ ≘ i.
#f #Hf #i elim i -i
[ /3 width=3 by gr_pat_eq_repl_back, gr_pat_refl/
| /3 width=7 by gr_pat_eq_repl_back, gr_pat_push/
]
qed.

(* Inversions with gr_eq *)

corec lemma gr_pat_inv_eq (f):
            (∀i. @❪i,f❫ ≘ i) → ⫯f ≡ f.
#Hf
lapply (Hf (𝟏)) #H
lapply (gr_pat_des_id … H) -H #H
cases H in Hf; -H #Hf
@gr_eq_push [3:|*: // ]
/3 width=7 by gr_pat_inv_succ_push_succ/
qed-.
