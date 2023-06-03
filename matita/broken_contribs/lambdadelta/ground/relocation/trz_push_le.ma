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

include "ground/relocation/trz_push.ma".
include "ground/relocation/trz_pnext_le.ma".

(* PUSH FOR TOTAL RELOCATION MAPS WITH INTEGERS *****************************)

(* Constuctions with zle ****************************************************)

lemma trz_push_dapp_gt_gt (f) (z):
      (𝟎) < z → (𝟎) < f＠⧣❨z❩ →
      ↑f＠⧣❨z❩ = (⫯f)＠⧣❨↑z❩.
#f #z #Hz #Hf
elim (zle_des_pos_sn … Hz) -Hz #p #H0 destruct
/2 width=1 by trz_puni_dapp_gt/
qed.
