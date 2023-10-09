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

include "ground/relocation/tz/tzr_tls.ma".
include "ground/relocation/tz/tzr_push_le.ma".

(* ITERATED TAIL FOR TOTAL RELOCATION MAPS WITH INTEGERS ********************)

(* Constructions with tzr_push **********************************************)

lemma tzr_tls_pos_unit_push_dapp_gt_gt (f) (z):
      (𝟎) < z → (𝟎) < f＠⧣❨z❩ →
      f＠⧣❨z❩ = (⫰*[⁤𝟏]⫯f)＠⧣❨z❩.
#f #z #H1z #H2z
<tzr_tls_dapp <tzr_push_dapp_pos_unit <tzr_push_dapp_gt_gt //
qed.
