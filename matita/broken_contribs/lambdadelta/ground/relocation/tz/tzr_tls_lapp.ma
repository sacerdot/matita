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

include "ground/relocation/tz/tzr_tls.ma".
include "ground/relocation/tz/tzr_lapp.ma".

(* ITERATED TAIL FOR TOTAL RELOCATION MAPS WITH INTEGERS ********************)

(* Constructions with tzr_lapp **********************************************)

lemma tzr_lapp_plus_dx (f) (z1) (z2):
      (⫰*[z2]f)＠§❨z1❩+f＠⧣❨z2❩ = f＠§❨z1+z2❩.
// qed.

lemma tzr_lapp_plus_sn (f) (z1) (z2):
      (⫰*[↑z2]f)＠⧣❨z1❩+f＠§❨z2❩ = f＠§❨z1+z2❩.
#f #z1 #z2
>zplus_succ_dx <tzr_dapp_plus >zplus_pred_dx //
qed.
