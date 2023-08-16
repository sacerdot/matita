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
include "ground/relocation/fb/fbr_xapp.ma".
include "ground/arith/nat_plus_rplus.ma".

(* UNIFORM ELEMENTS FOR FINITE RELOCATION MAPS WITH BOOLEANS ****************)

(* Constructions with fbr_xapp **********************************************)

(* Note: this dos not hold for k=𝟎 and n ≠ 𝟎 *)
lemma fbr_xapp_uni_pos (n) (k):
      (⁤k)+n = 𝐮❨n❩＠❨⁤k❩.
// qed.
