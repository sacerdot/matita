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
include "ground/relocation/fb/fbr_after.ma".

(* ITERATED RCONS FOR FINITE RELOCATION MAPS WITH BOOLEANS ******************)

(* Constructions with fbr_after *********************************************)

lemma fbr_after_pushs_rconss (b) (g) (f) (n):
      (g•f)◖*[n]b = (⫯*[n]g)•(f◖*[n]b).
#b #g #f #n @(nat_ind_succ … n) -n //
#n #IH
<fbr_rconss_succ >IH -IH
<fbr_rconss_succ <fbr_rconss_succ //
qed.

lemma fbr_after_nexts_sx (g) (f) (n):
      ↑*[n](g•f) = (↑*[n]g)•f.
#g #f #n @(nat_ind_succ … n) -n //
#n #IH <fbr_rconss_succ //
qed.
