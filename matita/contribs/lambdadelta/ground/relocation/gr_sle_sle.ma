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

(* INCLUSION FOR GENERIC RELOCATION MAPS ************************************)

(* Main constructions *******************************************************)

(*** sle_trans *)
corec theorem gr_sle_trans:
              Transitive … gr_sle.
#f1 #f * -f1 -f
#f1 #f #g1 #g #Hf #H1 #H #g2 #H0
[ cases (gr_sle_inv_push_sn … H0 … H) *
|*: cases (gr_sle_inv_next_sn … H0 … H)
] -g
/3 width=5 by gr_sle_push, gr_sle_next, gr_sle_weak/
qed-.
