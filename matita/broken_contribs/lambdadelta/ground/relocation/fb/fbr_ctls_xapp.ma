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

include "ground/relocation/fb/fbr_ctls_dapp.ma".
include "ground/relocation/fb/fbr_xapp.ma".
include "ground/arith/nat_plus_rplus.ma".
include "ground/arith/nat_rplus_pplus.ma".

(* ITERATED COARSE TAIL FOR FINITE RELOCATION MAPS WITH BOOLEANS ************)

(* Constructions with fbr_xapp **********************************************)

lemma fbr_xapp_plus (f) (m) (n):
      (⫰*[n]f)＠❨m❩+f＠❨n❩ = f＠❨m+n❩.
#f * // #p * // #q
<nplus_pos_sn <nplus_pos_sn <nrplus_pos_dx
>fbr_dapp_plus //
qed. 
