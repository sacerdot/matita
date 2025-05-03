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

include "ground/relocation/fb/fbr_lapp_eq.ma".
include "ground/relocation/fb/fbr_after_lapp.ma".
include "ground_2B/relocation/fbr_isafter.ma".

(* COMPOSITION CLASS FOR FINITE RELOCATION MAPS WITH BOOLEANS ***************)

(* Inversions with fbr_lapp *************************************************)

lemma fbr_isafter_inv_lapp (f1) (f2) (f) (n):
      f ϵ f2 ⊚ f1 → f＠§❨n❩ = f2＠§❨f1＠§❨n❩❩.
/2 width=1 by fbr_lapp_eq_repl/
qed-.

(* Destructions with fbr_lapp ***********************************************)
(*
lemma pr_after_des_nat_dx (f1) (f2) (f) (n1) (n2):
      f ϵ f2 ⊚ f1 →
      f2＠§❨n2❩ = f＠§❨n1❩ → n2 = f1＠§❨n1❩.
/2 width=6 by pr_after_des_pat_dx/ qed-.
*)
