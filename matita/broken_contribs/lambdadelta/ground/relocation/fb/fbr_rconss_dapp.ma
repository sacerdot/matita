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

include "ground/relocation/fb/fbr_rconss.ma".
include "ground/relocation/fb/fbr_dapp.ma".
include "ground/arith/nat_rplus_succ.ma".
include "ground/arith/nat_lt.ma".

(* ITERATED RCONS FOR FINITE RELOCATION MAPS WITH BOOLEANS ******************)

(* Constructions with fbr_dapp **********************************************)

lemma fbr_dapp_pushs_eq (f) (p):
      p = (⫯*[⁤p]f)＠⧣❨p❩.
#f #p elim p -p //
#p #IH
<fbr_rconss_pos <fbr_dapp_push_dx_succ //
qed.

lemma fbr_dapp_pushs_le (p) (n) (f):
      (⁤p) ≤ n → p = (⫯*[n]f)＠⧣❨p❩.
#p #n
@(nat_ind_succ … n) -n [| #n #IH ] #f #H0
[ lapply (nle_inv_zero_dx … H0) -H0 #H0 destruct
| elim (nle_split_lt_eq … H0) -H0 #H0 destruct //
  lapply (nlt_inv_succ_dx … H0) -H0 #H0
  <fbr_rconss_succ_swap <IH -IH //
]
qed-.

lemma fbr_dapp_nexts (f) (p) (n):
      f＠⧣❨p❩+n = (↑*[n]f)＠⧣❨p❩.
#f #p #n @(nat_ind_succ … n) -n //
#n #IH
<fbr_rconss_succ <fbr_dapp_next_dx <IH -IH //
qed. 
