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

include "ground/relocation/fb/fbr_after_dapp.ma".
include "ground/relocation/fb/fbr_xapp.ma".

(* COMPOSITION FOR FINITE RELOCATION MAPS WITH BOOLEANS *********************)

(* Constructions with fbr_xapp **********************************************)

lemma fbr_xapp_after (g) (f) (n):
      g＠❨f＠❨n❩❩ = (g•f)＠❨n❩.
#g #f * //
qed.
