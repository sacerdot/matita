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

include "ground/relocation/tr_uni.ma".
include "ground/relocation/tr_id_pap.ma".
include "ground/arith/nat_rplus_succ.ma".

(* UNIFORM ELEMENTS FOR TOTAL RELOCATION MAPS *******************************)

(* Coonstructions with tr_pap ***********************************************)

lemma tr_uni_pap_unit (n):
      ↑n = 𝐮❨n❩＠⧣❨𝟏❩.
// qed.

lemma tr_uni_pap (n) (p):
      p + n = 𝐮❨n❩＠⧣❨p❩.
#n @(nat_ind_succ … n) -n //
#n #IH * [| #p ] //
qed.
