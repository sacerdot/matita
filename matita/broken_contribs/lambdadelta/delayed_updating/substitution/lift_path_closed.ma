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
include "delayed_updating/substitution/lift_rmap_closed.ma".
include "ground/arith/nat_le_plus.ma".

(* LIFT FOR PATH ************************************************************)

(* Constructions with pcc ***************************************************)

lemma lift_path_closed_des_gen (f) (q) (n):
      q ϵ 𝐂❨n❩ → q = 🠡[f]q.
#f #q #n #Hq elim Hq -q -n //
#q #n #k #Hq #IH
<lift_path_d_dx <(lift_rmap_closed_xapp_le … Hq) -Hq //
qed-.

lemma lift_path_closed (f) (q) (n):
      q ϵ 𝐂❨n❩ → 🠡[f]q ϵ 𝐂❨n❩.
#f #q #n #Hq
<(lift_path_closed_des_gen … Hq) //
qed.

(* Inversions with pcc ******************************************************)

lemma lift_path_inv_closed (f) (q) (n):
      (🠡[f]q) ϵ 𝐂❨n❩ → q ϵ 𝐂❨n❩.
#f #q elim q -q //
* [ #k ] #q #IH #n
[ <lift_path_d_dx #H0
  lapply (pcc_inv_d_dx … H0) -H0 #H0
  >(lift_rmap_closed_xapp_le ??? k)
  [ /3 width=1 by pcc_d_dx/ |5,6: skip |
  | /2 width=1 by/ | skip
  ]
  /2 width=1 by nle_plus_dx_sn/
| <lift_path_L_dx #H0
  elim (pcc_inv_L_dx … H0) -H0 #H1 #H2 >H2 -H2
  /3 width=1 by pcc_L_dx/
| <lift_path_A_dx #H0
  /4 width=1 by pcc_A_dx, pcc_inv_A_dx/
| <lift_path_S_dx #H0
  /4 width=1 by pcc_S_dx, pcc_inv_S_dx/
]
qed-.
