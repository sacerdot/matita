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

include "ground/relocation/fb/fbr_rconss_ctl.ma".
include "ground/relocation/fb/fbr_rconss_plus.ma".
include "ground/relocation/fb/fbr_ctls_xapp.ma".

(* ITERATED RCONS FOR FINITE RELOCATION MAPS WITH BOOLEANS ******************)

(* Constructions with fbr_ctls **********************************************)

lemma fbr_ctls_pushs (f) (n):
      f = ⫰*[n]⫯*[n]f.
#f #n @(nat_ind_succ … n) -n //
#n #IH
<fbr_rconss_succ <fbr_ctls_succ_push //
qed.

lemma fbr_after_nexts_dx (n) (g) (f):
      ↑*[g＠❨n❩](⫰*[n]g•f) = g•↑*[n]f.
#n @(nat_ind_succ … n) -n //
#n #IH #g #f
<fbr_rconss_succ_swap <IH -IH
<fbr_after_next_dx >fbr_ctls_succ >fbr_rconss_plus //
qed.
