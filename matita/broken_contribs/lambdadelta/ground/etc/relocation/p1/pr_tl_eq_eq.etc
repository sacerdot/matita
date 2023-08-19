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

include "ground/relocation/p1/pr_tl_eq.ma".

(* TAIL FOR PARTIAL RELOCATION MAPS *****************************************)

(* Main constructions with pr_eq ********************************************)

(*** eq_trans *)
corec theorem pr_eq_trans: Transitive … pr_eq.
#f1 #f * -f1 -f
#f1 #f #g1 #g #Hf1 #H1 #H #f2 #Hf2
[ cases (pr_eq_inv_push_sn … Hf2 … H)
| cases (pr_eq_inv_next_sn … Hf2 … H)
] -g
/3 width=5 by pr_eq_push, pr_eq_next/
qed-.

(*** eq_canc_sn *)
theorem pr_eq_canc_sn (f2): pr_eq_repl_back (λf. f ≐ f2).
/3 width=3 by pr_eq_trans, pr_eq_sym/ qed-.

(*** eq_canc_dx *)
theorem pr_eq_canc_dx (f1): pr_eq_repl_fwd (λf. f1 ≐ f).
/3 width=5 by pr_eq_canc_sn, pr_eq_repl_sym/ qed-.
