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

include "ground/relocation/fb/fbr_after.ma".
include "ground/relocation/fb/fbr_dapp.ma".

(* COMPOSITION FOR FINITE RELOCATION MAPS WITH BOOLEANS *********************)

(* Constructions with fbr_dapp **********************************************)

lemma fbr_dapp_after (g) (f) (p):
      g＠⧣❨f＠⧣❨p❩❩ = (g•f)＠⧣❨p❩.
#g elim g -g //
* #g #IH
[ #f #p
  <fbr_after_next_sx <fbr_dapp_next_dx //
| * // * #f [ #p | * [| #p ]] //
  <fbr_after_push_rcons <fbr_dapp_push_dx_succ //
]
qed.
