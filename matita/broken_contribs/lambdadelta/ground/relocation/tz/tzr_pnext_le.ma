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

include "ground/relocation/tz/tzr_pnext.ma".
include "ground/relocation/tz/tzr_puni_le.ma".

(* POSITIVE NEXT FOR TOTAL RELOCATION MAPS WITH INTEGERS ********************)

(* Constuctions with zle ****************************************************)

lemma tzr_pnext_dapp_gt (f) (z):
      (𝟎) < f＠⧣❨z❩ →
      ↑f＠⧣❨z❩ = (↑⁺f)＠⧣❨z❩.
/2 width=1 by tzr_puni_dapp_gt/
qed.

lemma tzr_pnext_dapp_le (f) (z):
      f＠⧣❨z❩ ≤ 𝟎 →
      f＠⧣❨z❩ = (↑⁺f)＠⧣❨z❩.
/2 width=1 by tzr_puni_dapp_le/
qed.
