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

(* TAIL FOR GENERIC RELOCATION MAPS ***********************************************************)

(* Main properties with gr_eq **********************************************************)

(*** eq_trans *)
corec theorem gr_eq_trans: Transitive … gr_eq.
#f1 #f * -f1 -f
#f1 #f #g1 #g #Hf1 #H1 #H #f2 #Hf2
[ cases (gr_eq_inv_push_sn … Hf2 … H)
| cases (gr_eq_inv_next_sn … Hf2 … H)
] -g
/3 width=5 by gr_eq_push, gr_eq_next/
qed-.

(*** eq_canc_sn *)
theorem gr_eq_canc_sn (f2): gr_eq_repl_back (λf. f ≡ f2).
/3 width=3 by gr_eq_trans, gr_eq_sym/ qed-.

(*** eq_canc_dx *)
theorem gr_eq_canc_dx (f1): gr_eq_repl_fwd (λf. f1 ≡ f).
/3 width=5 by gr_eq_canc_sn, gr_eq_repl_sym/ qed-.
