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

include "ground/relocation/trz_tls.ma".
include "ground/relocation/trz_push_le.ma".

(* ITERATED TAIL FOR TOTAL RELOCATION MAPS WITH INTEGERS ********************)

(* Constructions with trz_push **********************************************)

lemma trz_tls_pos_unit_push_dapp_gt_gt (f) (z):
      (𝟎) < z → (𝟎) < f＠⧣❨z❩ →
      f＠⧣❨z❩ = (⫰*[⁤𝟏]⫯f)＠⧣❨z❩.
#f #z #H1z #H2z
<trz_tls_dapp <trz_push_dapp_pos_unit <trz_push_dapp_gt_gt //
qed.
