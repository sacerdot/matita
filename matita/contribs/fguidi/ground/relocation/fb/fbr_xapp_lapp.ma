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

include "ground/relocation/fb/fbr_xapp.ma".
include "ground/relocation/fb/fbr_lapp.ma".
include "ground/arith/nat_pred.ma".

(* EXTENDED DEPTH APPLICATION FOR FINITE RELOCATION MAPS WITH BOOLEANS ******)

(* Constructions with fbr_lapp **********************************************)

lemma fbr_lapp_xapp (f) (n):
      (⫰(f＠❨⁤↑n❩)) = f＠§❨n❩.
// qed.

lemma fbr_xapp_succ_lapp (f) (n):
      (⁤↑(f＠§❨n❩)) = f＠❨⁤↑n❩.
// qed.
