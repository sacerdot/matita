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

include "delayed_updating/substitution/lift_path.ma".
include "delayed_updating/syntax/path_closed.ma".
include "ground/relocation/xap.ma".

(* LIFT FOR PATH ************************************************************)

(* Constructions with pcc ***************************************************)

lemma lift_path_closed (f) (q) (n):
      q ϵ 𝐂❨n❩ → ↑[f]q ϵ 𝐂❨↑[q]f＠❨n❩❩.
#f #q #n #Hq elim Hq -Hq //
#q #n [ #k ] #_ #IH
/2 width=1 by pcc_d_dx, pcc_m_dx, pcc_L_dx, pcc_A_dx, pcc_S_dx/
qed.

lemma lift_path_rmap_closed (f) (p) (q) (n):
      q ϵ 𝐂❨n❩ → ↑[↑[p]f]q ϵ 𝐂❨↑[p●q]f＠❨n❩❩.
/2 width=1 by lift_path_closed/
qed.
