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

include "ground/relocation/fb/fbr_ctls.ma".
include "ground/relocation/fb/fbr_ctl_dapp.ma".

(* ITERATED COARSE TAIL FOR FINITE RELOCATION MAPS WITH BOOLEANS ************)

(* Constructions with fbr_dapp **********************************************)

lemma fbr_dapp_succ_sn (q) (f):
      (⫰*[⁤q]f)＠⧣❨𝟏❩+f＠⧣❨q❩ = f＠⧣❨↑q❩.
#q elim q -q //
#q #IH #f
<fbr_dapp_succ_dx <fbr_dapp_succ_dx >npsucc_pos <fbr_ctls_succ_swap
<pplus_assoc >IH -IH //
qed.

lemma fbr_dapp_plus (f) (q) (p):
      (⫰*[⁤q]f)＠⧣❨p❩+f＠⧣❨q❩ = f＠⧣❨p+q❩.
#f #q elim q -q //
#q #IH #p
<pplus_succ_shift <IH -IH
<fbr_dapp_succ_sn <fbr_dapp_succ_dx >fbr_ctls_succ //
qed. 
