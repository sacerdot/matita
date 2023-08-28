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

include "ground/relocation/fb/fbr_ctl.ma".
include "ground/relocation/fb/fbr_dapp.ma".
include "ground/arith/pnat_plus.ma".

(* COARSE TAIL FOR FINITE RELOCATION MAPS WITH BOOLEANS *********************)

(* Constructions with fbr_dapp **********************************************)

lemma fbr_dapp_succ_dx (f) (p):
      (⫰f)＠⧣❨p❩+f＠⧣❨𝟏❩ = f＠⧣❨↑p❩.
#f elim f -f //
* #f #IH // #p
<fbr_dapp_next_dx <fbr_dapp_next_dx <IH -IH //
qed.
