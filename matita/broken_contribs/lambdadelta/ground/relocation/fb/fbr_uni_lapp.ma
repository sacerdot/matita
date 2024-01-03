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

include "ground/relocation/fb/fbr_uni_dapp.ma".
include "ground/relocation/fb/fbr_lapp.ma".
include "ground/arith/nat_plus_rplus.ma".

(* UNIFORM ELEMENTS FOR FINITE RELOCATION MAPS WITH BOOLEANS ****************)

(* Constructions with fbr_lapp **********************************************)

lemma fbr_lapp_uni (n) (m):
      m+n = 𝐮❨n❩＠§❨m❩.
// qed.
