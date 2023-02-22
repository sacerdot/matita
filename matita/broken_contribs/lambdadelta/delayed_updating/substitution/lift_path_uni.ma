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

include "delayed_updating/substitution/lift_path_id.ma".
include "ground/relocation/tr_uni_pap.ma".
include "ground/relocation/tr_uni_tls.ma".
include "ground/arith/nat_pred_succ.ma".

(* LIFT FOR PATH ************************************************************)

(* Constructions with tr_uni ************************************************)

lemma lift_path_d_sn_uni (p) (n) (k):
      (𝗱(k+n)◗p) = 🠡[𝐮❨n❩](𝗱k◗p).
#p #n #k
<lift_path_d_sn <tr_uni_pap >nsucc_pnpred
<tr_tls_succ_uni //
qed.
