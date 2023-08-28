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

include "ground/relocation/fb/fbr_ctls_xapp.ma".
include "ground/relocation/fb/fbr_xapp_lapp.ma".
include "ground/arith/nat_pred_succ.ma".

(* ITERATED COARSE TAIL FOR FINITE RELOCATION MAPS WITH BOOLEANS ************)

(* Constructions with fbr_lapp **********************************************)

lemma fbr_lapp_plus_dx_xapp (f) (m) (n):
      (⫰*[⁤↑n]f)＠❨m❩+f＠§❨n❩ = f＠§❨m+n❩.
#f #m #n
<fbr_lapp_xapp in ⊢ (???%);
>nplus_succ_dx <fbr_xapp_plus
<fbr_xapp_succ_lapp <nplus_succ_dx //
qed.

lemma fbr_lapp_plus_sn_xapp (f) (m) (n):
      (⫰*[n]f)＠§❨m❩+f＠❨n❩ = f＠§❨m+n❩.
#f #m #n
<fbr_lapp_xapp in ⊢ (???%);
>nplus_succ_sn <fbr_xapp_plus
<fbr_xapp_succ_lapp <nplus_succ_sn //
qed.
