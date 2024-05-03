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
include "ground/relocation/fb/fbr_ctl.ma".
include "ground/relocation/fb/fbr_after.ma".
include "ground/relocation/fb/fbr_dapp.ma".

(* ITERATED RCONS FOR FINITE RELOCATION MAPS WITH BOOLEANS ******************)

(* Constructions with fbr_ctl ***********************************************)

lemma fbr_after_next_dx (g) (f):
      ↑*[⁤(g＠⧣❨𝟏❩)]((⫰g)•f) = g•↑f.
#g elim g -g //
* #g #IH #f //
<fbr_after_next_sn <fbr_dapp_next_dx <fbr_rconss_pos <IH -IH //
qed.
