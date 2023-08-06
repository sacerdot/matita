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

(* ITERATED RCONS FOR FINITE RELOCATION MAPS WITH BOOLEANS ******************)

(* Constructions with fbr_dapp **********************************************)

lemma fbr_dapp_nexts (f) (p) (n):
      f＠⧣❨p❩+n = (↑*[n]f)＠⧣❨p❩.
#f #p #n @(nat_ind_succ … n) -n //
#n #IH
<fbr_rconss_succ <fbr_dapp_next_dx <IH -IH //
qed. 
