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

include "ground/relocation/tz/tzr_puni.ma".
include "ground/arith/int_lt_pred.ma".

(* POSITIVE UNIFORM ELEMENTS FOR TOTAL RELOCATION MAPS WITH INTEGERS ********)

(* Constuctions with zle ****************************************************)

lemma tzr_puni_dapp_gt (z):
      (𝟎) < z →
      ↑z = 𝐮⁺＠⧣❨z❩.
#z #Hz
elim (zle_des_pos_sn … Hz) -Hz //
qed.

lemma tzr_puni_dapp_le (z):
      z ≤ 𝟎 →
      z = 𝐮⁺＠⧣❨z❩.
#z #Hz
elim (zle_split_lt_eq … Hz) -Hz #Hz
[ elim (zlt_des_zero_dx … Hz) -Hz //
| destruct //
]
qed.
