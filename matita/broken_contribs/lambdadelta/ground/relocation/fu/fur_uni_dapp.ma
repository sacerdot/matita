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

include "ground/relocation/fu/fur_uni.ma".
include "ground/relocation/fu/fur_dapp.ma".

(* UNIFORM ELEMENTS FOR FINITE RELOCATION MAPS FOR UNWIND *******************)

(* Constructions with fur_dapp **********************************************)

lemma fur_dapp_uni (p) (n):
      p+n = 𝐮❨n❩＠⧣❨p❩.
// qed.
