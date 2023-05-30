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
include "delayed_updating/substitution/lift_path_eq.ma".
include "ground/relocation/trz_uni_tls.ma".

(* LIFT FOR PATH ************************************************************)

(* Constructions with trz_uni ***********************************************)

lemma lift_path_d_sn_uni (p) (n) (k):
      (𝗱(k+n)◗p) = 🠡[𝐮❨n❩](𝗱k◗p).
#p #n #k
<lift_path_d_sn <trz_uni_unfold
<(lift_path_eq_repl … (trz_tls_uni …)) //
qed.
