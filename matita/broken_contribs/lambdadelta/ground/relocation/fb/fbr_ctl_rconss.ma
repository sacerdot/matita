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

include "ground/relocation/fb/fbr_ctl.ma".
include "ground/relocation/fb/fbr_rconss.ma".

(* COARSE TAIL FOR FINITE RELOCATION MAPS WITH BOOLEANS *********************)

(* Constructions with fbr_rconss ********************************************)

lemma fbr_ctl_nexts (f) (n):
      (⫰f) = (⫰↑*[n]f).
#f #n @(nat_ind_succ … n) -n //
#n #IH
<fbr_rconss_succ <fbr_ctl_next //
qed.
