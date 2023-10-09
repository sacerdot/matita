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

include "ground/relocation/p1/pr_sle.ma".

(* INCLUSION FOR PARTIAL RELOCATION MAPS ************************************)

(* Main constructions *******************************************************)

(*** sle_trans *)
corec theorem pr_sle_trans:
              Transitive … pr_sle.
#f1 #f * -f1 -f
#f1 #f #g1 #g #Hf #H1 #H #g2 #H0
[ cases (pr_sle_inv_push_sn … H0 … H) *
|*: cases (pr_sle_inv_next_sn … H0 … H)
] -g
/3 width=5 by pr_sle_push, pr_sle_next, pr_sle_weak/
qed-.
