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

include "ground/relocation/fb/fbr_uni.ma".
include "ground/relocation/fb/fbr_rconss_dapp.ma".

(* UNIFORM ELEMENTS FOR FINITE RELOCATION MAPS WITH BOOLEANS ****************)

(* Constructions with fbr_dapp **********************************************)

lemma fbr_dapp_uni (n) (p):
      p+n = 𝐮❨n❩＠⧣❨p❩.
// qed.

(* Note: this is used in systems originating from λσ *)
lemma fbr_dapp_uni_unit (p):
      p = 𝐮❨↓p❩＠⧣❨𝟏❩.
// qed.
