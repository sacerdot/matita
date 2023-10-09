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

include "ground/relocation/fb/fbr_xapp.ma".
include "ground/relocation/fb/fbr_rconss_dapp.ma".

(* ITERATED RCONS FOR FINITE RELOCATION MAPS WITH BOOLEANS ******************)

(* Constructions with fbr_xapp **********************************************)

lemma fbr_xapp_pushs_le (f) (k) (n):
      k ≤ n → k = (⫯*[n]f)＠❨k❩.
#f * // #p #n #H0
<fbr_xapp_pos <(fbr_dapp_pushs_le … H0) -H0 //
qed-.
